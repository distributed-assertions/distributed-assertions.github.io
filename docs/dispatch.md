# Dispatch: Join the DAMF with ease

**Dispatch** is an Intermediary tool for publishing, retrieval, and trust analysis in the Distributed Assertion Management Framework (DAMF).

## Obtaining and Building

### Source

- [Zip][dispatch-zip]
- [Github][dispatch-repo]

[dispatch-zip]: https://github.com/distributed-assertions/dispatch/archive/refs/heads/main.zip
[dispatch-repo]: https://github.com/distributed-assertions/dispatch

### Requirements

- [`Kubo`][kubo] - previously known as `ipfs-go`
- [`nodejs`][nodejs]

[kubo]: https://github.com/ipfs/kubo
[nodejs]: https://nodejs.org/en/

### Building

1. In the root directory of **Dispatch**, run:

    `% npm install`

2. Then run:

    `% npm run build`

Generated executables for `linux`, `macOS`, and `Microsoft Windows` shall be found at the `executables/` directory.

----------------

## Commands

Calling `dispatch` will list the available commands. Using `dispatch <command> -h` lists more information about each command and its arguments.

### Configuration

#### create-agent

*Description*

    create an agent profile with a public-private key pair.

*Usage*

Call `create-agent <agent-profile-name>` to create an *agent profile* in the local `.config/dispatch/agentprofiles.json` file. An agent profile object contains a generated public-private key pair (the parameters for this generation are currently fixed), and it's referred by its name in the [publish](#publish) command.

#### create-tool

*Description*

    create a tool profile from a new description or from an existing tool cid.

*Usage*

Call `create-tool <tool-profile-name> <input-type> <input>` to create a *tool profile* in the local `.config/dispatch/toolprofiles.json` file. A tool profile object contains the cid for the *tool object*, and it's referred by its name in the [publish](#publish) command.

The `<input-type>` argument takes one of three possible values:

1. `file`: in case the `<input>` for the tool description is a file.
2. `json`: in case the `<input>` for the tool description is a `json` file.
3. `cid`: in case the profile is created for an existing *tool object*. In such case, the `<input>` would be the tool object's cid.

In (1) and (2), this command will [publish](#publish) the described tool as a *tool object* and use the corresponding cid.

#### create-language

*Description*

    create a language profile from a new description or from an existing language cid.

*Usage*

Call `create-language <language-profile-name> <input-type> <input>` to create a *language profile* in the local `.config/dispatch/languages.json` file. A language profile object contains the cid for the *language object*, and it's referred by its name in the [publish](#publish) command.

The `<input-type>` argument takes one of three possible values:

1. `file`: in case the `<input>` for the language description is a file.
2. `json`: in case the `<input>` for the language description is a `json` file.
3. `cid`: in case the profile is created for an existing *language object*. In such case, the `<input>` would be the language object's cid.

In (1) and (2), this command will [publish](#publish) the described language as a *language object* and use the corresponding cid.

#### set-web3token

*Description*

    set personal web3.storage api token.

*Usage*

#### set-gateway

*Description*

    set gateway for retrieval.

*Usage*

#### list-config

*Description*

    list configuration parameters.

*Usage*

### Publishing

#### publish

*Description*

*Usage*

### Retrieval

#### get

*Description*

*Usage*

### Trust Analysis

#### lookup

*Description*

*Usage*
