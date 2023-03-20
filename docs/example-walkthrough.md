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

```{.coq .downloadable title="FibLemma.v" linenums="1"}
Require Import Arith.
--8<-- "docs/example-files/FibLemma.v:2:11"
```

We will prove our lemma of interest using the `lia` tactic of Coq, which is
enabled by the `Lia` module. We will also pervasively use rewriting modulo
linear arithmetic identities, so we define a Ltac named `liarw` for convenience.

```{.coq .continued title="FibLemma.v" linenums="12"}
Require Import Lia.
--8<-- "docs/example-files/FibLemma.v:12:15"
```

Finally, here is our full proof of the lemma, which is named `fib_square_above`
here. This lemma itself makes use of a different lemma called `fib_square_lemma`.

```{.coq .continued title="FibLemma.v" linenums="17"}
--8<-- "docs/example-files/FibLemma.v:17:"
```

<!-- [Download <tt>FibLemma.v</tt>](/FibLemma.v){ class="md-button" } -->

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

```{.json .downloadable title="Coq.language.content.json" linenums="1"}
--8<-- "docs/example-files/Coq.language.content.json"
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

<!-- [Download <tt>Coq.language.content.json</tt>](/Coq.language.content.json){ class="md-button" } -->

We can record that we used Coq v.8.16.1 to verify our proofs of the assertions
by referencing a DAMF tool object in the `mode` field of the corresponding
production. Like with the language object above, there isn't currently a
standard DAMF tool object to represent this version of the Coq
implementation. Therefore, like with languages above, we will create the content
of such a tool object ourselves for the purposes of this walkthrough.

```{.json .downloadable title="coq-8.16.1.tool.content.json" linenums="1"}
--8<-- "docs/example-files/coq-8.16.1.tool.content.json"
```

To create the DAMF tool object, we use `dispatch create-tool`.

```console
$ dispatch create-tool coq-8.16.1 json coq-8.16.1.tool.content.json
Tool profile coq-8.16.1 created successfully!
```

<!-- [Download <tt>coq-8.16.1.tool.content.json</tt>](/coq-8.16.1.tool.content.json){ class="md-button" } -->

### 5. The DAMF assertions

There is currently no software that can transform the theorems we have just
proved in Coq into DAMF assertions. We will do this manually. To cause the least
breakage, we will reuse the text of the Coq development as much as possible.

Consider the first lemma, `fib_square_lemma`. The _formula_ content of this
lemma is the string `"forall n, 2 * n + 27 <= fib (n + 12)"`. This string,
however, only makes sense in a _context_ where the symbols `*`, `+`, `<=`,
`fib`, etc. are defined. These symbols come from the Coq standard prelude with
some additional support from the `Arith` module, except `fib` which we defined
ourselves. Thus, the DAMF context object for this formula can be built with the
following input for Dispatch:

```json linenums="1"
{
  "format": "context",
  "language": "coq-8.16.1", // (1)!
  "content": [
    "Require Arith",
    "Fixpoint fib (n: nat): nat := match … end" // (2)!
  ]
}
```

1. This is the local name we picked using `dispatch create-language` in step 4.
2. Lines 3--11 of `FibLemma.v`.

In order to buil the assertion that corresponds to `fib_square_lemma`, Dispatch
expects the formulas and contexts to be laid out using local names. Here, we can
use the name `fib_square_lemma` as the local name of the formula, and
`fib_square_lemma!context` as the local name of its context. Then, in the
production underlying the assertion we use the local name `coq-8.16.1` for the
_mode_ field, which is the local name of the DAMF tool object we created in step 4.
The complete assertion is as follows, again as a Dispatch input.

```json linenums="1"
{
  "format": "assertion",
  "agent": "exampleAgent", // (1)!
  "claim": {
    "format": "annotated-production",
    "annotation": { "name": "fib_square_lemma" }, // (2)!
    "production": {
      "mode": "coq-8.16.1", // (3)!
      "sequent": {
        "conclusion": "fib_square_lemma", // (4)!
        "dependencies": [ ]
      }
    }
  },
  "formulas": {
    "fib_square_lemma": {
      "language": "coq-8.16.1",
      "context": "fib_square_lemma!context", // (5)!
      "content": "forall n, 2 * n + 27 <= fib (n + 12)"
    }
  },
  "context": {
    "fib_square_lemma!context": {
      "language": "coq-8.16.1",
      "content": [
        "Require Arith",
        "Fixpoint fib (n: nat): nat := match … end"
      ]
    }
  }
}
```

1. We made this with `dispatch create-agent` in step 2.
2. This defines a possible name for the assertion, but it only serves as a hint
   for consumers. The actual global name is the CID of the DAMF assertion object
   that Dispatch will create. This annotation object can have other metadata
   besides this name himt, such as the Coq proof script. Its structure is not
   prescribed by DAMF.
3. This is the local name we picked using `dispatch create-tool` in step 4.
4. This points to the formula object defined in the `"formulas"` section below
   (lines 16--20).
5. This points to the context object defined in the `"contexts"` section below
   (lines 23--29).

We can of course ask Dispatch to publish only this assertion. However, since we
have two assertions in this file, it is more convenient for Dispatch to publish
both assertions together as a DAMF collection. Here is what it looks like:

```{.json .max30 .downloadable title="FibLemma.v.assertions.json" linenums="1"}
--8<-- "docs/example-files/FibLemma.v.assertions.json"
```

We can now use Dispatch to publish the entire collection at once.

```console
$ dispatch publish FibLemma.v.assertions.json local # (1)!
published collection object of cid: bafyreigsngij2hdpxpeqktvmmjo6pxckkobynldhh5mqvbey66xhdixrey
```

1. `local` means that it is being published to the local IPFS repository we set up in step 1.

This CID can be [explored in IPLD explorer][explore].

[explore]: https://explore.ipld.io/#/explore/bafyreigsngij2hdpxpeqktvmmjo6pxckkobynldhh5mqvbey66xhdixrey

## Computations with λProlog

TODO

## Theorem in Abella DAMF

TODO

<script>
  (async function () {
    for (const el of document.getElementsByClassName("downloadable")) {
      const th = el.getElementsByTagName("th")[0];
      const span = th.getElementsByTagName("span")[0];
      const fileName = span.innerHTML;
      span.innerHTML = `${ fileName } (<a href="/example-files/${ fileName }">download</a>)`;
    }
    for (const el of document.getElementsByClassName("continued")) {
      const th = el.getElementsByTagName("th")[0];
      const span = th.getElementsByTagName("span")[0];
      const fileName = span.innerHTML;
      span.innerHTML = `${ fileName } (contd.)`;
    }
  })();
</script>
