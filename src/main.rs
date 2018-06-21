/*
 *  Copyright © 2018 Gianmarco Garrisi
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
extern crate petgraph;
extern crate rand;
#[macro_use] extern crate quicli;
extern crate rayon;

use quicli::prelude::*;

use rayon::join;

use petgraph::prelude::*;
use petgraph::algo::astar;

use rand::prelude::*;
use rand::distributions::Range;
use rand::XorShiftRng;

#[derive(Copy, Clone, Debug)]
struct Link {
    capacity: f64,
    const_power: f64,
    var_power: f64
}

#[derive(Copy, Clone, Debug)]
struct Node {
    const_power: f64,
    var_power: f64
}

#[derive(Copy, Clone, Debug)]
struct LogicLink {
    tot_power: f64,
    usage: f64,
    capacity: f64 
}

fn parse_seed(seed: &str) -> [u8;16] {
    let mut seed:u128 = seed.parse().expect("Unable to parse random seed");
    let mut parsed = [0;16];
    for i in 1..=16 {
        parsed[4-i] = (seed & std::u8::MAX as u128) as u8;
        seed = seed >> 8;
    }
    parsed
}

/// Heuristically compute a solution for the green networking problem
#[derive(StructOpt, Debug)]
struct Interface{
    /// Number of nodes in the network
    #[structopt(long="nodes", short="n")]
    n: usize,
    /// Number of nodes in a row of the grid
    #[structopt(long="row", short="r")]
    r: usize,
    /// Random seed. The traffic is genearated using a seeded random number generator,
    /// in order to be consistent between two run. You can change it to change the result
    /// of the computation. Can be an integer ranging from 1 up to 340,282,366,920,938,463,463,374,607,431,768,211,455
    #[structopt(long="seed", short="s", default_value="1234", parse(from_str="parse_seed"))]
    seed: [u8;16],
}

main!(|args:Interface|{
    let mut rng = XorShiftRng::from_seed(args.seed);

    let traffic = create_logical_topology(args.n, &mut rng);
    let physical = create_grid_physical_topology(args.n, args.r);

    let logical = route_all_over(&traffic, &physical);

    // we can run the two algorithms in parallel
    let (rmp, rlu) = join(|| most_power(&logical, &physical), || least_used(&logical, &physical));
    // and then select the best result
    let res = if rmp.1 > rlu.1 {
        rlu
    } else {
        rmp
    };

    println!("Total power usage: {}", res.1);
});

fn create_logical_topology(nodes:usize, rng: &mut XorShiftRng) -> Graph<usize, f64>{
    // Create a logical topology that describes the traffic from one node to each other.
    let mut logic = Graph::new();

    for i in 0..nodes {
        logic.add_node(i);
    }
    let traffic_values = Range::new(0.0, 1.0);

    for from in 0usize..nodes {
        for to in (0usize..nodes).filter(|&a| a != from) {
            logic.add_edge(NodeIndex::new(from), NodeIndex::new(to), traffic_values.sample(rng));
        }
    }
    logic
}

fn create_grid_physical_topology(n:usize, r:usize) -> Graph<Node, Link> {
    if n%r != 0 {
        panic!("Cannot build a grid topology with the given dimentions");
    }
    let c = n/r;
    let mut physical = Graph::new();
    for _ in 0usize..n {
        let n = Node{const_power: 0.5, var_power:0.7};
        physical.add_node(n);
    }

    let add_left = |physical:&mut Graph<_,_>, i| {
        if i % r != 0{
            let l = Link{capacity:n as f64, const_power:0.2, var_power:0.4};
            physical.add_edge(NodeIndex::new(i), NodeIndex::new(i - 1), l);
        }
    };
    let add_right = |physical:&mut Graph<_,_>, i| {
        if i%r != r-1 {
            let l = Link{capacity:n as f64, const_power:0.2, var_power:0.4};
            physical.add_edge(NodeIndex::new(i), NodeIndex::new(i + 1), l);
        }
    };
    let add_up = |physical:&mut Graph<_,_>, i| {
        if i/r != 0 {
            let l = Link{capacity:n as f64, const_power:0.2, var_power:0.4};
            physical.add_edge(NodeIndex::new(i), NodeIndex::new(i - r), l);
        }
    };
    let add_down = |physical:&mut Graph<_,_>, i| {
        if i/r != c-1 {
            let l = Link{capacity:n as f64, const_power:0.2, var_power:0.4};
            physical.add_edge(NodeIndex::new(i), NodeIndex::new(i + r), l);
        }
    };
    for i in 0usize..n {
        add_left(&mut physical, i);
        add_right(&mut physical, i);
        add_up(&mut physical, i);
        add_down(&mut physical, i);
    }

    physical
}

fn route_all_over(traffic: &Graph<usize, f64>, physical: &Graph<Node, Link>) -> Graph<i32, LogicLink> {
    let mut logical = Graph::from_edges(physical.raw_edges().iter()
                                        .map(|e| (e.source(), e.target(),
                                                  LogicLink{tot_power: 0.0,
                                                            capacity: e.weight.capacity,
                                                            usage: 0.0})));
    for tsd in traffic.raw_edges().iter() {
        let path = astar(&physical, tsd.source(), |n| n == tsd.target(), |_| 1, |_| 0).unwrap().1;
        let mut a = tsd.source();
        for n in path.iter().skip(1) {
            let eix = logical.find_edge(a, *n).unwrap();
            let link = physical[physical.find_edge(a, *n).unwrap()];
            let node_a = physical[a];
            let node_b = physical[*n];
            let w = logical.edge_weight_mut(eix).unwrap();
            if w.tot_power == 0.0 {
                w.tot_power += link.const_power;
            }
            w.tot_power += link.var_power * tsd.weight;
            w.tot_power += node_a.var_power * tsd.weight;
            w.tot_power += node_b.var_power * tsd.weight;
            w.usage += tsd.weight;
            a = *n;
        }
    }

    logical
}

use std::cmp::{PartialOrd, Ordering};

fn most_power(logical: &Graph<i32, LogicLink>, physical: &Graph<Node, Link>) -> (Graph<i32, LogicLink>, f64) {
    let mut edges = Vec::from(logical.raw_edges());
    edges.par_sort_unstable_by(|e1, e2| {
        match e2.weight.tot_power.partial_cmp(&e1.weight.tot_power) {
            Some(o) => o,
            None => Ordering::Equal,
        }
    });

    let mut logical = logical.clone();
    let min = edges.last().unwrap().weight.tot_power;

    for e in edges {
        // check the total power consumption
        let total_power_before:f64 = total_power_usage(&logical);
        // remove the edges that consumes more power
        let ix = logical.find_edge(e.source(), e.target()).unwrap();
        logical.remove_edge(ix).unwrap();
        // compute the new shortest path
        let sp =
            if let Some(p) = astar(&logical, e.source(), |n| n==e.target(),
                                   |er| er.weight().tot_power, |_| min) {
                p.1
            } else {
                continue
            };
        // start the computation of the power usage after the removal of the arc
        let mut total_power_after = total_power_before - e.weight.tot_power;
        let mut feasible = true;
        {
            // check the feasibility of the new solution
            let mut a = sp.first().unwrap();
            for n in sp.iter().skip(1) {
                let ix = logical.find_edge(*a, *n).unwrap();
                let w = logical.edge_weight_mut(ix).unwrap();
                if w.capacity/2.0 < w.usage + e.weight.usage {
                    // unfeasible solution
                    feasible = false;
                    break
                }
                // update the power consumption after the operation
                total_power_after += physical[*a].var_power * e.weight.usage;
                total_power_after += physical[*n].var_power * e.weight.usage;
                let ix = physical.find_edge(*a, *n).unwrap();
                total_power_after += physical[ix].var_power * e.weight.usage;
                a = n;
            }
        }
        // If the removal of an arc brings to a feasible solution that uses less power,
        // we can proceed to the update of all the edges on the new computed path...
        if feasible && total_power_after < total_power_before {
            let mut a = *sp.first().unwrap();
            for n in sp.into_iter().skip(1) {
                let ix = logical.find_edge(a, n).unwrap();
                let w = logical.edge_weight_mut(ix).unwrap();
                w.usage += e.weight.usage;
                w.tot_power += physical[a].var_power * e.weight.usage;
                w.tot_power += physical[n].var_power * e.weight.usage;
                let ix = physical.find_edge(a, n).unwrap();
                w.tot_power += physical[ix].var_power * e.weight.usage;
                a = n;
            }
        }
        // otherwise, we put the arc back and try another one
        else {
            logical.add_edge(e.source(), e.target(), e.weight);
        }
    }
    let tmp = total_power_usage(&logical);
    (logical, tmp)
}

fn least_used(logical: &Graph<i32, LogicLink>, physical: &Graph<Node, Link>) -> (Graph<i32, LogicLink>, f64){
    let mut edges = Vec::from(logical.raw_edges());
    edges.par_sort_unstable_by(|e1, e2| {
        match e1.weight.usage.partial_cmp(&e2.weight.usage) {
            Some(o) => o,
            None => Ordering::Equal,
        }
    });

    let mut logical = logical.clone();
    let min = edges.last().unwrap().weight.tot_power;

    for e in edges {
        // check the total power consumption
        let total_power_before:f64 = total_power_usage(&logical);
        // remove the edges that consumes more power
        let ix = logical.find_edge(e.source(), e.target()).unwrap();
        logical.remove_edge(ix).unwrap();
        // compute the new shortest path
        let sp =
            if let Some(p) = astar(&logical, e.source(), |n| n==e.target(),
                                   |er| er.weight().tot_power, |_| min) {
                p.1
            } else {
                continue
            };
        // start the computation of the power usage after the removal of the arc
        let mut total_power_after = total_power_before - e.weight.tot_power;
        let mut feasible = true;
        {
            // check the feasibility of the new solution
            let mut a = sp.first().unwrap();
            for n in sp.iter().skip(1) {
                let ix = logical.find_edge(*a, *n).unwrap();
                let w = logical.edge_weight_mut(ix).unwrap();
                if w.capacity/2.0 < w.usage + e.weight.usage {
                    // unfeasible solution
                    feasible = false;
                    break
                }
                // update the power consumption after the operation
                total_power_after += physical[*a].var_power * e.weight.usage;
                total_power_after += physical[*n].var_power * e.weight.usage;
                let ix = physical.find_edge(*a, *n).unwrap();
                total_power_after += physical[ix].var_power * e.weight.usage;
                a = n;
            }
        }
        // If the removal of an arc brings to a feasible solution that uses less power,
        // we can proceed to the update of all the edges on the new computed path...
        if feasible && total_power_after < total_power_before {
            let mut a = *sp.first().unwrap();
            for n in sp.into_iter().skip(1) {
                let ix = logical.find_edge(a, n).unwrap();
                let w = logical.edge_weight_mut(ix).unwrap();
                w.usage += e.weight.usage;
                w.tot_power += physical[a].var_power * e.weight.usage;
                w.tot_power += physical[n].var_power * e.weight.usage;
                let ix = physical.find_edge(a, n).unwrap();
                w.tot_power += physical[ix].var_power * e.weight.usage;
                a = n;
            }
        }
        // otherwise, we put the arc back and try another one
        else {
            logical.add_edge(e.source(), e.target(), e.weight);
        }
    }
    let tmp = total_power_usage(&logical);
    (logical, tmp)
}

fn total_power_usage(logical: &Graph<i32, LogicLink>) -> f64 {
    logical.raw_edges().par_iter()
            .map(|e| e.weight.tot_power)
            .sum()
}
