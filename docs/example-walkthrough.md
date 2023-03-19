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

This walkthrough will perform this verification task using the following
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

$ dispatch list-config | grep exampleAgent # (1)!
  exampleAgent: {
    name: 'exampleAgent',
```

1. Just to verify that it worked.

## Lemma in Coq

In order to follow along with this walkthrough, you should [install Coq
version 8.16.1](https://coq.inria.fr/download).

### 3. Full proof

We begin with a traditional (_autarkic_) mode of usage of Coq, unmodified,
without any connection to DAMF assertions.

As usual, we begin with importing the `Arith` module to fix the interpretation
of numerals using the `nat` type, and then capture $\kop{fib}$ as the recursive
fixed point function `fib`.

```coq title="FibLemma.v" linenums="1"
Require Import Arith.
--8<-- "docs/FibLemma.v:2:11"
```

We will prove our lemma of interest using the `lia` tactic of Coq, which is
enabled by the `Lia` module. We will also pervasively use rewriting modulo
linear arithmetic identities, so we define a Ltac named `liarw` for convenience.

```coq title="FibLemma.v" linenums="12"
Require Import Lia.
--8<-- "docs/FibLemma.v:12:15"
```

Finally, here is our full proof of the lemma, which is named `fib_square_above`
here. This lemma itself makes use of a different lemma called `fib_square_lemma`.

```coq title="FibLemma.v" linenums="17"
--8<-- "docs/FibLemma.v:17:"
```

[Download <tt>FibLemma.v</tt>](/FibLemma.v){ class="md-button" }

### 4. Language and Tool Objects

Let's move on to representng `fib_square_lemma` and `fib_square_above` as DAMF
assertions.

To get there, we first have to turn Coq propositions into DAMF formula objects,
for which we will need to supply a suitable `language` field. As there isn't
(yet!) a universally agreed upon DAMF object to represent this language, we will
create one for the purposes of this walkthrough.

We start by creating a JSON object to represent the `content` of what a "Coq
version 8.16.1" language object might contain. Here we could in principle link
to the reference manual that is distributed as part of the Coq 8.16.1
release. We could alternatively, or in addition, place the source or exceutable
code of a Coq parser. In this walkthrough, to simplify matters, we will
represent this language as the following JSON object that just links to the Coq
website.

```js title="Coq.language.content.json" linenums="1"
--8<-- "docs/Coq.language.content.json"
```

We can then use `dispatch create-language` to make the DAMF language object and
simultaneously give it a local human-readable name, `coq-8.16.1`.

```console
$ dispatch create-language coq-8.16.1 json Coq.language.content.json
Language record coq-8.16.1 created successfully!
```

If we want to see the DAMF object that was created by Dispatch, we can read its
`languages.json` configuration file to get its CID, and then use `ipfs dag get`
to explore the contents of the linked objects in IPLD starting from that CID.

```console
$ cat $HOME/.config/dispatch/languages.json
{"coq-8.16.1":{"name":"coq-8.16.1","language":"bafy…rxxy"}}

$ ipfs dag get bafy…rxxy # (1)!
{"content":{"/":"bafy…mj5u"},"format":"language"}

$ ipfs dag get bafy…rxxy/content # (2)!
{"name":"Coq","url":"https://coq.inria.fr","version":"8.16.1"}
```

1. This is the CID found in `languages.json`.
2. This is isomorphic to our `Coq.language.content.json` object.

[Download <tt>Coq.language.content.json</tt>](/Coq.language.content.json){ class="md-button" }

We can record that we used Coq v.8.16.1 to verify our proofs of the assertions
by referencing a DAMF tool object in the `mode` field of the corresponding
production. Like with the language object above, there isn't currently a
standard DAMF tool object to represent this version of the Coq
implementation. Therefore, like with languages above, we will create the content
of such a tool object ourselves for the purposes of this walkthrough.

```js title="coq-8.16.1.tool.content.json" linenums="1"
--8<-- "docs/coq-8.16.1.tool.content.json"
```

To create the DAMF tool object, we use `dispatch create-tool`.

```console
$ dispatch create-tool coq-8.16.1 json coq-8.16.1.tool.content.json
Tool profile coq-8.16.1 created successfully!
```

[Download <tt>coq-8.16.1.tool.content.json</tt>](/coq-8.16.1.tool.content.json){ class="md-button" }

### 5. The DAMF assertions

TODO

## Computations with λProlog

TODO

## Theorem in Abella DAMF

TODO
