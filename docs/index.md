---
title: DAMF
authors:
  - Farah Al Wardani
  - Kaustuv Chaudhuri
  - Dale Miller
---
# Distributed Assertion Management Framework

![DAMF Logo](/assets/logo/damf.png){ width="60" }
The _Distributed Assertion Management Framework_ (DAMF) is a proposed collection
of formats and techniques to enable heterogeneous formal reasoning systems and
users to communicate _assertions_ in a decentralized, reliable, and egalitarian
manner. An _assertion_ is a unit of mathematical knowledge---think lemmas,
theorems, corollaries, etc.---that is cryptographically signed by its
originator.

The philosophy of DAMF is explained in this technical report:

> Farah Al Wardani, Kaustuv Chaudhuri, and Dale Miller (2023). _[Distributing
> and trusting proof checking: a preliminary report][alwardani22hal]_.

[alwardani22hal]: https://hal.inria.fr/hal-03909741

The technical construction of DAMF is explained in this draft paper:

> Farah Al Wardani, Kaustuv Chaudhuri, and Dale Miller (2023). _[Formal
> Reasoning using Distributed Assertions][cade23draft]_. Submitted: 2023-05-22.

[cade23draft]: /assets/papers/draft23damf2.pdf

DAMF is based on content-addressable storage using the _[InterPlanetary File
System][ipfs]_ (IPFS) network, and uses the _[InterPlanetary Linked Data][ipld]_
(IPLD) data model to represent assertions and all their components.

[ipfs]: https://ipfs.tech
[ipld]: https://ipld.io

:mag_right:  Explore the proposed **[DAMF Formats](/damf-formats/)**.

:aerial_tramway: Read about **[Processes](/damf-processes/)** in DAMF.

:rocket: Install **[Dispatch](/dispatch/)**, an intermediary tool that helps in integrating systems.

:wrench: Experiment with some edge systems. In particular:

- **[Abella DAMF](/abella/)**, a version of [Abella](https://abella-prover.org) with DAMF support.
- [λProlog](/lprolog/) integrated with DAMF.

:walking: Read an **[example walkthrough](/example-walkthrough/)** of using a heterogeneous
  combination of systems to prove an assertion.
