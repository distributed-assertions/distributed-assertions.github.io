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

* [Abella DAMF](./abella.md) for the overall theorem
* [Coq](https://coq.inria.fr) to prove the lemma
* [λProlog](./lprolog.md) to illustrate how to incorporate logic programming

## Setup

### 1. Local IPFS client

[DAMF](./index.md) is built on top of IPFS and IPLD, so you will need an IPFS client. For
this walkthrough we will use the [Dispatch](./dispatch.md) intermediary, which
requires the [Kubo](https://github.com/ipfs/kubo) desktop program accessed via
the command `ipfs`.

* [Installation instructions for Kubo desktop](https://docs.ipfs.tech/install/ipfs-desktop)

You will also need to create your local IPFS repository, usually stored under
`$HOME/.ipfs` or a similar folder. This is done by issuing the following
command: `ipfs init`.

```{.console .conbox}
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

The [Dispatch](./dispatch.md) intermediate tool can be used to create an _agent
profile_, which is just a human-readable string that stands for an agent.  Agent
profile names are _not_ globally shared using IPFS. Indeed, DAMF is completely
unaware of agent profiles.

In this walkthrough, we will create an agent profile called
`exampleAgent`. Install Dispatch by [following the
instructions](./dispatch.md/#obtaining-and-building). In the rest of this tutorial,
we will use the command `dispatch` to stand for whichever Dispatch executable is
relevant to your system. Next, run `dispatch create-agent`.

```{.console .conbox}
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
--8<-- "./docs/example-files/FibLemma.v:2:11"
```

We will prove our lemma of interest using the `lia` tactic of Coq, which is
enabled by the `Lia` module. We will also pervasively use rewriting modulo
linear arithmetic identities, so we define a Ltac named `liarw` for convenience.

```{.coq .continued title="FibLemma.v" linenums="12"}
Require Import Lia.
--8<-- "./docs/example-files/FibLemma.v:12:15"
```

Finally, here is our full proof of the lemma, which is named `fib_square_above`
here. This lemma itself makes use of a different lemma called `fib_square_lemma`.

```{.coq .continued title="FibLemma.v" linenums="17"}
--8<-- "./docs/example-files/FibLemma.v:17:"
```

<!-- [Download <tt>FibLemma.v</tt>](/FibLemma.v){ class="md-button" } -->

### 4. Language and Tool objects

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
--8<-- "./docs/example-files/Coq.language.content.json"
```

We can then use `dispatch create-language` to make the DAMF language object and
simultaneously give it a local human-readable name, `coq-8.16.1`.

```{.console .conbox}
$ dispatch create-language coq-8.16.1 json Coq.language.content.json
Language record coq-8.16.1 created successfully!
```

If we want to see the DAMF object that was created by Dispatch, we can read its
`languages.json` configuration file to get its CID, and then use `ipfs dag get`
to explore the contents of the linked objects in IPLD starting from that CID.

```{.console .conbox}
$ cat $HOME/.config/dispatch/languages.json
{"coq-8.16.1":{"name":"coq-8.16.1","language":"bafyreiayvr5klyi25dq2wrjqg2dwlgmxwsoxg2tcv7tdy675h5u7wtrxxy"}}

$ ipfs dag get bafyreiayvr5klyi25dq2wrjqg2dwlgmxwsoxg2tcv7tdy675h5u7wtrxxy # (1)!
{"content":{"/":"bafyreidmf3nxeigvi7mfklzu2wr7oapa7fodqdeajbxtngy5ax7cccmj5u"},"format":"language"}

$ ipfs dag get bafyreiayvr5klyi25dq2wrjqg2dwlgmxwsoxg2tcv7tdy675h5u7wtrxxy/content # (2)!
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
--8<-- "./docs/example-files/coq-8.16.1.tool.content.json"
```

To create the DAMF tool object, we use `dispatch create-tool`.

```{.console .conbox}
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

In order to build the assertion that corresponds to `fib_square_lemma`, Dispatch
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
  "contexts": {
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
--8<-- "./docs/example-files/FibLemma.v.assertions.json"
```

We can now use Dispatch to publish the entire collection at once.

```{.console .conbox}
$ dispatch publish FibLemma.v.assertions.json local # (1)!
Published DAMF collection object to local with cid: bafyreigdthmeok6gwsdulovqrgvzz4tbad2ifjxpa74dlpbfbt7ehnkyha
```

1. `local` means that it is being published to the local IPFS repository we set up in step 1.

This CID can be [explored in IPLD explorer][explore-coq]. It can also be locally
explored with `ipfs dag get`:

```{.console .conbox}
$ ipfs dag get bafyreigdthmeok6gwsdulovqrgvzz4tbad2ifjxpa74dlpbfbt7ehnkyha | python -m json.tool # (1)!
{
    "elements": [
        {
            "/": "bafyreicpwpxl3xe4nefsqc3f2rdxiedxjbmekh25m5cgqkriwp3qsivope"
        },
        {
            "/": "bafyreigscd65tb2rabcpjxbep7h4lklbyfenmj32ioond7ouhh7qpvkh7a"
        }
    ],
    "format": "collection",
    "name": "FibLemma.v"
}

$ ipfs dag get bafyreic53degjxdfn7e2l3spleevftr5pxemr7ydspkvwimr4smhjqjzuy/elements/0/claim/production/sequent/conclusion/content
"forall n, 2 * n + 27 <= fib (n + 12)"
```

1. `python -m json.tool` is being used to pretty-print the JSON

[explore-coq]: https://explore.ipld.io/#/explore/bafyreic53degjxdfn7e2l3spleevftr5pxemr7ydspkvwimr4smhjqjzuy

## Computations with λProlog

Another way of building assertions is by means of a computational engine. Here
we will give the example of using λProlog to perform computations on natural
numbers.  Coq is of course more than capable of doing these computations by
itself, so the purpose of this section is mainly to illustrate how we can
incorporate assertions from different sources.

### 6. Logic programming

Like with Coq earlier, let us quickly sketch how we are going to represent and
compute with natural numbers in λProlog. We declare `nat` as a new type with the
`kind` keyword in the signature, then declare two constants `z` and `s` as the
constructors of `nat`. Note that λProlog operates under the _open world
assumption_, so there is no way to declare that these are the only two
constructors for `nat`. The signature also declares three _predicates_, which
are constants with target type `o`, which is the type of λProlog formulas.
Here are the signature (`fib.sig`) and module (`fib.mod`) files.

=== "Signature"

    ```{.lprolog .downloadable title="fib.sig" linenums="1"}
    --8<-- "./docs/example-files/fib.sig"
    ```

=== "Module"

    ```{.lprolog .downloadable title="fib.mod" linenums="1"}
    --8<-- "./docs/example-files/fib.mod"
    ```

We will use the [Teyjus](https://github.com/teyjus/teyjus) implementation of
λProlog, which compiles a module (a `.sig`/`.mod` pair) to bytecode that can be
executed using a bytecode interpreter. To compile the above module `fib`, we run:

```{.console .conbox}
$ tjcc fib && tjlink fib
```

Then, we can execute queries against `fib` by using `tjsim`.

```{.console .conbox}
$ tjsim fib
Welcome to Teyjus
⋮
[fib] ?- fib (s (s (s (s (s (s z)))))) X.

The answer substitution:
X = s (s (s (s (s (s (s (s z)))))))

More solutions (y/n)? n

yes

[fib] ?-
```

It is also possible to run `tjsim` in batch (non-interactive) mode, where the
query is specified in the command line.

```{.console .conbox}
$ tjsim -b -m 1 -s 'fib (s (s (s (s (s (s z)))))) X.' fib # (1)!

The answer substitution:
X = s (s (s (s (s (s (s (s z)))))))
```

1. **b**atch mode, **m**aximum one solution, **s**olve query

### 7. Exporting to DAMF

We use the following language and tool descriptions for λProlog and Teyjus (version 2.1.1):

=== "Language"

    ```{.json .downloadable title="lprolog.language.content.json" linenums="1"}
    --8<-- "./docs/example-files/lprolog.language.content.json"
    ```

=== "Tool"

    ```{.json .downloadable title="teyjus-2.1.1.tool.content.json" linenums="1"}
    --8<-- "./docs/example-files/teyjus-2.1.1.tool.content.json"
    ```

=== "Dispatch commands"

    ```{.console .conbox}
    $ dispatch create-language lprolog json lprolog.language.content.json
    Language record lprolog created successfully!

    $ dispatch create-tool teyjus-2.1.1 json teyjus-2.1.1.tool.content.json
    Tool profile teyjus-2.1.1 created successfully!
    ```

To build the DAMF assertions, we can use the following _harness_ module:
[<tt>harness.sig</tt>](./example-files/harness.sig) and
[<tt>harness.mod</tt>](./example-files/harness.mod).  The purpose of the harness
module is to turn a sequence of goals for a module `FILE`, written in a file
`FILE.goals`, into a JSON file `FILE.json` that can be given to `dispatch
publish`. Note that the agent, language, and tool names that we chose with
`dispath create-agent`, `dispatch create-language`, and `dispatch create-tool`
respectively, are directly written in the harness module.

To use the harness, we define a module `main` that accumulates and compiles the
`fib` and `harness` modules.

=== "Signature"

    ```{.lprolog .downloadable title="main.sig" linenums="1"}
    --8<-- "./docs/example-files/main.sig"
    ```

=== "Module"

    ```{.lprolog .downloadable title="main.mod" linenums="1"}
    --8<-- "./docs/example-files/main.mod"
    ```

The file `fib.goals` is a list of goals, with each goal wrapped in a name using
the `name` predicate. For our purposes, we can just list goals that compute
$\kop{fib}(n)$ and $n^2$ for $n$ between 1 and 13.

```{.lprolog .downloadable title="fib.goals" linenums="1"}
--8<-- "./docs/example-files/fib.goals"
```

Finally, here's how we can run `harness`, and subsequently Dispatch:

```{.console .conbox}
$ tjcc fib && tjcc harness && tjcc main && tjlink main

$ tjsim -b -s 'damf_export.' -m 1 main
Wrote fib.json.

$ dispatch publish fib.json local # (1)!
Published DAMF collection object to local with cid: bafyreickai4hsl3aht53hz3veen5xlzvx7njy7sudsfpns3ikxtnuzpjha
```

1. Can take a few dozen seconds to finish.

This CID can be [explored on IPLD explorer][explore-lp] or locally with `ipfs dag get`.

[explore-lp]: https://explore.ipld.io/#/explore/bafyreickai4hsl3aht53hz3veen5xlzvx7njy7sudsfpns3ikxtnuzpjha

## Theorem in Abella DAMF

The assertions generated by Coq and λProlog will be used to prove the main
theorem in [Abella DAMF](./abella.md), which is a variant of the [Abella theorem
prover](https://abella-prover.org/) that can accept and publish DAMF assertions.

Abella is simply typed and its type system does not have any reasoning
principles that yield theorems. Reasoning in Abella is done with its _reasoning
logic_ known as $\mathcal{G}$, which is an extension of first-order
intuitionistic logic over $\lambda$-terms that supports inductive and
co-inductive definitions, generic quantification (using $\nabla$), and nominal
abstraction (a generalization of $\alpha\beta\eta$ equality on $\lambda$-terms).

### 8. Setting the stage

We will write the overall theorem in the Abella file
[<tt>FibTheorem.thm</tt>](./example-files/FibTheorem.thm). It begins by defining
the type `nat` of natural numbers, its constructors `z` and `s`, and then some
comparison relations and computations. Note that all definitions in Abella are
relational: unlike Coq, we don't define `+` as a binary function on natural
numbers but as a ternary relation `plus` that relates its first two arguments to
its third.

```{.abella .downloadable title="FibTheorem.thm" linenums="1"}
--8<-- "./docs/example-files/FibTheorem.thm::30"
```

Because all inductive definitions are relational in Abella, we often need
additional lemmas to establish that the relations behave like functions. In our
theorem we will need the following lemmas of this kind.

```{.abella .continued title="FibTheorem.thm" linenums="30"}
--8<-- "./docs/example-files/FibTheorem.thm:30:63"
```

### 9. Importing DAMF assertions

Abella can import any DAMF assertion using the following statement:

```abella
Import "damf:<cid>".
```

Here, `<cid>` can be the CID of an individual DAMF assertion object or a DAMF
collection object containing assertions. If these assertion objects are in
Abella's own language, they can be used as is. For reference, Abella's DAMF
language object has the following CID:

```
bafyreic7eqwwwbjtrbcz4fj33wdoyt6qext6ji46vggwjjliznyzvaymoy
```

What about the case of DAMF assertions in a different language? In this case,
Abella will need to use an _adapter sequent_ as explained in the [DAMF technical
design paper](https://doi.org/10.1007/978-3-031-43369-6_10). In the future, such adapter
sequents will be built using language translation tools. For now, we will write
the adapter sequents ourselves and sign the resulting assertions using a `mode`
field of `null`, which stands for an assertion for which the signing agent is
wholly responsible.

To create such adapter sequents, Abella has a modified form of the `Import
... as` statement that allows the user to restate the theorem in Abella's own
language.  For example, the theorem `fib_square_above` from Coq that was
exported in step 5 can be imported in Abella as follows:

```{.abella .continued title="FibTheorem.thm" linenums="63"}
--8<-- "./docs/example-files/FibTheorem.thm:65:69"
```

The statement of this theorem needs to be comprehensible in the local context of
the Abella development, using the type `nat`, constants `s` and `z`, and the
relations `times`, `fib`, `lt`, etc. defined in lines 1--29 of
<tt>FibTheorem.thm</tt>.

!!! info "Iterated application notation"

    The term `s^13 z` stands for the term
    `(s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))`,
    which is 13 in the unary representation of `nat`. For any unary term
    constant `k` and literal number `n` ($\ge 0$), the notation `(k^n t)`
    stands for the `n`-times iterated application of `k` to `t`.

After type-checking the statement of the theorem, Abella uses this `Import
... as` statement first to build the adapter sequent that has the following DAMF
structure:

```{.json}
{ "format": "assertion",
  "claim": {
    "format": "annotated-production",
    "annotation": {
      "name": "fib_square_above!adapter"
      "generator": "damf:bafyreiegwjyj5f2lpw3ck35pqeqt45bwl57c7n7xfpbtxm6ym3sfsixixq" // (1)!
    },
    "production": {
      "mode": null,
      "sequent": {
        "conclusion": "fib_square_above",
        "dependencies": [
          "damf:bafyreigscd65tb2rabcpjxbep7h4lklbyfenmj32ioond7ouhh7qpvkh7a/claim/production/sequent/conclusion" // (2)!
        ] } }
  "formulas": {
    "fib_square_above": {
      "language": "damf:bafyreic7eqwwwbjtrbcz4fj33wdoyt6qext6ji46vggwjjliznyzvaymoy", // (3)!
      "content": "forall x, nat x -> … -> lt y u",
      "context": "fib_square_above!context"
    } },
  "contexts": {
    "fib_square_above!context": {
      "language": "damf:bafyreic7eqwwwbjtrbcz4fj33wdoyt6qext6ji46vggwjjliznyzvaymoy",
      "content": [
        "Kind nat type", "Type z nat", "Type s nat -> nat",
        "Define nat : …", "Define leq : …", "Define lt : …",
        "Define times : …", "Define fib : …"
      ] } } }
```

1. This field links to the DAMF tool object for this version of Abella. Because
   it is part of an annotation, DAMF prescribes no particular meaning to the
   `"generator"` key or its value. Its purpose in this walkthrough is purely
   documentary in nature.
2. This uses IPLD paths to refer to the CID of the `conclusion` of the assertion
   object that was imported. It corresponds to the theorem named `fib_square_above`
   that we proved in Coq.
3. This is the Abella language's identifier

This adapter sequent, which has a dependency on an external formula in a
different language (Coq) to the conclusion (Abella), will be published using
Dispatch. For the rest of the file, Abella then continues as if
`fib_square_lemma` was indeed stated and proved in Abella.

The assertions produced using λProlog in step 7 are similarly imported using a
sequence of `Import ... as` statements.

```{.abella .continued .max30 title="FibTheorem.thm" linenums="68"}
--8<-- "./docs/example-files/FibTheorem.thm:70:145"
```

### 10. Finishing the theorem

Assembling the final theorem in Abella is now straightforward. In the _only if_
direction (forward), we repeatedly make use of the computation assertions from
λProlog for $n \in 0..12$, and then the `fib_square_above` assertion for $n \ge
13$. In the _if_ direction, we just verify that the computations (again, pulled
from λProlog) have the right values.

```{.abella .continued title="FibTheorem.thm" linenums="142"}
--8<-- "./docs/example-files/FibTheorem.thm:146:"
```

Verifying this in Abella requires the `--damf-imports` command line
flag. Publishing the assertions also requires the `--damf-publish <location>`
flag, where `<location>` is either `local` or `cloud`.

```{.console .conbox}
$ abella --damf-imports --damf-publish local FibTheorem.thm
Published as damf:bafyreifg3cosrvpidfmepwsjjt6kwvrlb2iobe5wo27sqsbu5uzbrdlvhm
```

As usual, this can be [browsed in IPLD explorer][explore-abella].

[explore-abella]: https://explore.ipld.io/#/explore/bafyreifg3cosrvpidfmepwsjjt6kwvrlb2iobe5wo27sqsbu5uzbrdlvhm

<script>
  (async function () {
    for (const el of document.getElementsByClassName("downloadable")) {
      const th = el.getElementsByTagName("th")[0];
      const span = th.getElementsByTagName("span")[0];
      const fileName = span.innerHTML;
      span.innerHTML = `${ fileName } (<a target="_blank" href="./example-files/${ fileName }">download</a>)`;
    }
    for (const el of document.getElementsByClassName("continued")) {
      const th = el.getElementsByTagName("th")[0];
      const span = th.getElementsByTagName("span")[0];
      const fileName = span.innerHTML;
      span.innerHTML = `${ fileName } (contd.)`;
    }
  })();
</script>
