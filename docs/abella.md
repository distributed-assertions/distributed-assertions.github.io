# Abella DAMF

**Abella DAMF** is a branch of the [Abella theorem
prover](https://abella-prover.org) that is designed to use and publish [DAMF](/)
assertions.

### Obtaining and Building

You need a working [OCaml](https://ocaml.org) distribution with some standard
accompanying software such as [OPAM](https://opam.ocaml.org),
[Dune](dune.readthedocs.io/), and [OCaml
findlib](https://github.com/ocaml/ocamlfind). The instructions below are for a
recent OCaml (&ge;4.14.0) and OPAM (&ge;2.1.2), do the following:

1. Clone the [Abella repository](https://github.com/abella-prover/abella) on Github:
   ~~~~bash
   $ git clone https://github.com/abella-prover/abella.git
   ~~~~
2. From the `abella` directory, run these commands:
   ~~~~bash
   $ git checkout ipfs
   $ opam pin -y .
   ~~~~
   This pin will override the existing Abella package in OPAM (if any).
3. To uninstall this version of Abella and restore the standard Abella packages
   in OPAM, run in the same `abella` directory as step 2 above:
   ~~~~bash
   $ opam uninstall -y abella
   $ opam unpin .
   ~~~~

### Using

1. Prerequisite: you must setup [Dispatch](/software/dispatch/). In particular:
   * You will need to know the path to the Dispatch executable.
   * You will need to create, at minimum, an agent profile using `dispatch create-agent`.
2. Place the following in `$XDG_CONFIG_HOME/abella/config.json` (creating the
   containing directory if it doesn't exist). If `$XDG_CONFIG_HOME` is not
   defined in your environment, use `$HOME/.config/abella/config.json` instead.
   ~~~~js
   {
     "damf.dispatch": "/path/to/dispatch-executable",
     "damf.agent": "agent-profile-name"
   }
   ~~~~
   Replace the values with the path to the Dispatch executable and the name of
   your agent profile you created in step 1.
3. Abella DAMF currently only runs in batch mode, meaning that you can only
   process entire `.thm` files at a time. DAMF mode is enabled with the
   following switches:
     * `--damf-imports`: this will enable `Import "damf:..."` statements.
     * `--damf-publish DEST`: to enable publishing DAMF assertions signed with
       your agent profile. `DEST` is one of the following:
         - `local` (for your local IPFS store, managed by whichever IPFS daemon you
           use, e.g., Kupo)
         - `cloud` (for publishing through `web3.storage`; see the
           [Dispatch](/software/dispatch/) documentation for details)
