# An optimizer for the Green Networking problem

This program implement a solver for the design of an energy efficient network.

In particular, the power consumption is considered composed by two factors:
* The load on the device
* The on/off state of the device.

Both links and nodes are considered devices that dissipate energy.

This is a greedy heuristic algorithm that tries to minimize the power consumption on a grid topology avoiding to overload the links. The traffic is randomly generated. 

This software makes some use of mutlithreading, when it was not too difficult to add it.
For example, it runs two optimization algorithms concurrently.

## Complexity
The complexity of this algorithm is given by the one of the shortest path routing: **O(4N^3+N^3logN) ~ O(N^3)**.
The optimization runs in **O(16N^2 + 4N^2logN) ~ O(N^2)**

## Credits
It has been developed together by:
* Silvia Bova
* Gianmarco Garrisi
* Nicol Macaluso
* Ruben Monti
