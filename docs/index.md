# Distributed Assertion Management Framework (DAMF)

![image info](./assets/logo/damf.png){ width="60" }
The _Distributed Assertion Management Framework_ (DAMF) is a proposed collection
of formats and techniques to enable heterogeneous formal reasoning systems and
users to communicate _assertions_ in a decentralized, reliable, and egalitarian
manner. An _assertion_ is a unit of mathematical knowledge: think lemmas,
theorems, corollaries, etc.

The philosophy of DAMF is explained in this technical report:

> Farah Al Wardani, Kaustuv Chaudhuri, and Dale Miller (2023). _[Distributing
> and trusting proof checking: a preliminary report][alwardani22hal]_.

[alwardani22hal]: https://hal.inria.fr/hal-03909741

The technical construction of DAMF is explained in this draft paper:

> Farah Al Wardani, Kaustuv Chaudhuri, and Dale Miller (2023). _[Formal
> Reasoning using Distributed Assertions][cade23draft]_. Submitted: 2023-02-28.

[cade23draft]: /assets/papers/draft23damf.pdf

DAMF is based on content-addressable storage using the _[InterPlanetary File
System][ipfs]_ (IPFS) network, and uses the _[InterPlanetary Linked Data][ipld]_
(IPLD) data model to represent assertions and all their components.

[ipfs]: https://ipfs.tech
[ipld]: https://ipld.io
