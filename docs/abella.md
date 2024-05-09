# Abella DAMF

**Abella DAMF** is a branch of the [Abella theorem
prover](https://abella-prover.org) that is designed to use and publish [DAMF](./index.md)
assertions.

### Obtaining and Building

You need a working [OCaml][ocaml] distribution with some standard accompanying
software such as [OPAM][opam], [Dune][dune], and [findlib][ocamlfind]. The
instructions below are for a recent OCaml (&ge;4.14.0) and OPAM (&ge;2.1.2).

[ocaml]: https://ocaml.org/
[dune]: https://dune.build/
[ocamlfind]: https://github.com/ocaml/ocamlfind
[opam]: https://opam.ocaml.org

1. Clone the [Abella repository](https://github.com/abella-prover/abella):
   ~~~~bash
   % git clone https://github.com/abella-prover/abella.git
   ~~~~
2. From the `abella` directory, run these commands:
   ~~~~bash
   % git checkout f931011d4da6d654f846aa9dc71fe00788196961
   % opam pin -y .
   ~~~~
   The SHA used in the `git checkout` command corresponds to the currently used commit within the `ipfs` branch.
   The `opam pin` command will override (reversibly) the existing Abella package in OPAM if any,
   then build and install Abella to your OPAM environment. You can then launch Abella
   through the command `$(opam var bin)/abella` -- or just `abella` if you have set
   up your OPAM environment correctly.
   ~~~~
   % $(opam var bin)/abella -v
   2.0.9-ipfs
   ~~~~

    Note that you can instead directly download [this Zip](../docs/assets/zips/abella-f931011d4da6d654f846aa9dc71fe00788196961.zip) and proceed from the `opam pin -y .` command.

3. To uninstall this version of Abella and restore the standard Abella packages
   in OPAM, run in the same `abella` directory as step 2 above:
   ~~~~bash
   % opam uninstall -y abella
   % opam unpin .
   ~~~~

### Using

1. Limitations:
     * Abella DAMF only runs in batch mode, i.e., it can only process a single
       `.thm` file at a time in a non-interactive session.
     * Abella DAMF currently _does not_ support the specification language. In
       other words, you cannot use the `Specification` command. This limitation
       will be relaxed soon. All other features of the reasoning language of
       Abella are supported.
2. Prerequisite: you must setup [Dispatch](./dispatch.md). In particular:
     * You will need to know the path to the Dispatch executable.
     * You will need to create, at minimum, an agent profile using `dispatch create-agent`.
3. Place the following in `$XDG_CONFIG_HOME/abella/config.json` (creating the
   containing directory if it doesn't exist). If `$XDG_CONFIG_HOME` is not
   defined in your environment, use `$HOME/.config/abella/config.json` instead.
   ~~~~js
   {
     "damf.dispatch": "/path/to/dispatch-executable",
     "damf.agent": "agent-profile-name"
   }
   ~~~~
   Replace the values with the path to the Dispatch executable and the name of
   your agent profile you created in step 2.
4. DAMF mode is enabled with the following switches:
     * `--damf-imports`: this will enable the `Import "damf:..."` top-level
       command.
     * `--damf-publish DEST`: to enable publishing DAMF assertions signed with
       your agent profile. `DEST` is one of the following:
         - `local` (for your local IPFS store, managed by whichever IPFS daemon you
           use, e.g., Kupo)
         - `cloud` (for publishing through [web3.storage][w3s]; see the
           [Dispatch](./dispatch.md) documentation for details)

[w3s]: https://web3.storage/
