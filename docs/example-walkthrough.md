---
title: Example
---
# Example Walkthrough

This walkthrough shows how to use a combination of DAMF-aware edge systems to
verify and subsequently publish the following assertion:

!!! success ""

    **Theorem.** For $n \in \mathbb{N}$, $\kop{fib}(n) = n^2$ if and only if $n \in
    \{0, 1, 12\}$, where $\kop{fib}(n)$ stands for the $n$th Fibonacci
    number defined as:
    $\kop{fib}(0) \triangleq 0$,
    $\kop{fib}(1) \triangleq 1$, and
    $\kop{fib}(n + 2) \triangleq \kop{fib}(n + 1) + \kop{fib}(n)$.

In the _if_ direction, the assertion is fairly easy to prove in any system that
can support inductive definitions such as $\kop{fib}$ in the first place: one
just has to compute $\kop{fib}(0)$, $\kop{fib}(1)$, and $\kop{fib}(12)$ and
verify that they are indeed $0$, $1$, and $144$, respectively. The _only if_
direction, on the other hand, requires the ability to reason about the growth of
the Fibonacci function with respect to the quadratic function $n \mapsto n^2$.
In particular, one needs the following lemma:

!!! tip ""

    **Lemma.** For $n \in \mathbb{N}$, if $n \ge 13$, then $\kop{fib}(n) > n^2$.

This walkthrough will perform this verification tasks using the following
heterogeneous collection of systems:

* [Abella DAMF](/abella/) for the overall theorem
* [Coq](https://coq.inria.fr) to prove the lemma
* [λProlog](/lprolog/) to illustrate how to incorporate logic programming

## Setup

### 1. Local IPFS client

[DAMF](/) is built on top of IPFS and IPLD, so you will need an IPFS client. For
this walkthrough we will use the [Dispatch](/dispatch/) intermediary, which
requires the [Kubo](https://github.com/ipfs/kubo) desktop program accessed via
the command `ipfs`.

* [Installation instructions for Kubo desktop](https://docs.ipfs.tech/install/ipfs-desktop)

You will also need to create your local IPFS repository, usually stored under
`$HOME/.ipfs` or a similar folder. This is done by issuing the following
command: `ipfs init`.

```console
$ ipfs init
generating ED25519 keypair...done
peer identity: 12D3KooWNEsJFEp4FM14o9zedmFpBohUA4jPH77WYex75YP6mNHk
initializing IPFS node at /home/ExampleUser/.ipfs
to get started, enter:

	ipfs cat /ipfs/QmQPeNsJPyVWPFDVHb77w8G42Fvo15z4bG2X8D2GhfbSXc/readme

```

!!! info "IPFS Daemon"

    Running the IPFS daemon is optional for this walkthrough.
    You only need the daemon if you want to disseminate the assertions you
    publish into the IPFS network so that other people may use them.
    If you leave the daemon off, you will only be able to share assertions
    between programs that can access your local IPFS repository.

### 2. Dispatch, agent profile

In DAMF, all assertions are _signed_ by exactly one _agent_. Concretely, an
agent is a public-private key pair; the _name_ of the agent is just its
public key.

The [Dispatch](/dispatch/) intermediate tool can be used to create an _agent
profile_, which is just a human-readable string that stands for an agent.  Agent
profile names are _not_ globally shared using IPFS. Indeed, DAMF is completely
unaware of agent profiles.

In this walkthrough, we will create an agent profile called
`exampleAgent`. Install Dispatch by [following the
instructions](/dispatch/#obtaining-and-building). In the rest of this tutorial,
we will use the command `dispatch` to stand for whichever Dispatch executable is
relevant to your system. Next, run `dispatch create-agent`.

```console
$ dispatch create-agent exampleAgent
Agent profile exampleAgent created successfully!

$ dispatch list-config | grep exampleAgent       # just to verify
  exampleAgent: {
    name: 'exampleAgent',
```

## Lemma in Coq

TODO

## Computations with λProlog

TODO

## Theorem in Abella DAMF
