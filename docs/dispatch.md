# Dispatch: Join the DAMF with ease

**Dispatch** is an Intermediary tool for publishing, retrieval, and trust analysis in the Distributed Assertion Management Framework (DAMF).

It is based on the [DAMF Formats](/damf-formats/) specification and implements the main [DAMF processes](/damf-processes/). It is intended to be usable by both human users and tools.

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

**Dispatch** consists of a collection of CLI commands. Running the `dispatch` executable will list the available commands. Using `dispatch <command> -h` lists more information about each command and its arguments.

### Configuration

#### create-agent

*Description*

    create an agent profile with a public-private key pair.

*Usage*

Run `dispatch create-agent <agent-profile-name>` to create an *agent profile* in the local `.config/dispatch/agentprofiles.json` file. An agent profile object contains a generated public-private key pair (the parameters for this generation are currently fixed), and it's referred by its name in the [publish](#publish) command.

:warning: **Caution**. Remember to keep your private key *private*.

#### create-tool

*Description*

    create a tool profile from a new description or from an existing tool cid.

*Usage*

Run `dispatch create-tool <tool-profile-name> <input-type> <input>` to create a *tool profile* in the local `.config/dispatch/toolprofiles.json` file. A tool profile object contains the cid for the *tool object*, and it's referred by its name in the [publish](#publish) command.

The `<input-type>` argument takes one of three possible values:

1. `file`: in case the `<input>` for the tool description is a file.
2. `json`: in case the `<input>` for the tool description is a `json` file.
3. `cid`: in case the profile is created for an existing *tool object*. In such case, the `<input>` would be the tool object's cid.

In (1) and (2), this command will [publish](#publish) the described tool as a *tool object* and use the corresponding cid.

#### create-language

*Description*

    create a language profile from a new description or from an existing language cid.

*Usage*

Run `dispatch create-language <language-profile-name> <input-type> <input>` to create a *language profile* in the local `.config/dispatch/languages.json` file. A language profile object contains the cid for the *language object*, and it's referred by its name in the [publish](#publish) command.

The `<input-type>` argument takes one of three possible values:

1. `file`: in case the `<input>` for the language description is a file.
2. `json`: in case the `<input>` for the language description is a `json` file.
3. `cid`: in case the profile is created for an existing *language object*. In such case, the `<input>` would be the language object's cid.

In (1) and (2), this command will [publish](#publish) the described language as a *language object* and use the corresponding cid.

#### set-web3token

*Description*

    setup a personal web3.storage API token.

*Usage*

**Dispatch** initially publishes objects through the local IPFS daemon, and pins them *locally* on the local IPFS node. This means that initial requests to get a `cid` will have to retrieve it from the publisher's local IPFS node, which could be a bit slow at the beginning. In order to make the retrieval process faster, **Dispatch** uses the [web3.storage](https://web3.storage) service as a *pinning service* that serves in making published objects more easily discoverable through the IPFS network.

In order to use this service:

1. Create a [web3.storage account](https://web3.storage/login/) and [generate an API token](https://web3.storage/docs/how-tos/generate-api-token/).

    :warning: **Caution**. This API token shall be known only to the account's user(s).

2. Run `dispatch set-web3token <token>` with the generated API token as an argument.

Using this service is optional and decided by the user when invoking the [publish](#publish) command.

#### set-gateway

*Description*

    setup a gateway for retrieval.

*Usage*

Starting from a `cid`, **Dispatch** initially tries to retrieve the corresponding DAG through the local IPFS daemon. If the retrieval was unsuccessful, **Dispatch** tries to use a *gateway* to aid in this process.

Think of a *gateway* as a *well-connected* IPFS node that can discover stuff faster. More about gateways and their usage can be found at the [IPFS official docs](https://docs.ipfs.tech/concepts/ipfs-gateway).

The default gateway is set to `https://dweb.link`.

To set a different gateway, run `dispatch set-gateway <gateway>`. Note that the specified gateway should support the IPFS DAG API.

#### list-config

*Description*

    list configuration parameters.

*Usage*

Run `dispatch list-config` to display the configuration parameters.

### Publishing

#### Input formats

As illustrated in [DAMF Formats](/damf-formats/), the *global shared objects* shall follow the specified DAMF formats: *assertion*, *production*, *sequent*, *formula*, etc.

**Dispatch** provides an *interface* for users (human users or tools) to the DAMF store through a collection of standard input formats. These standard inputs are produced by users, then processed and published by *Dispatch* as DAMF objects. In this way, a user does not have to interact with IPFS in any form.

Examples of these formats can be found at the [dispatch github repository](https://github.com/distributed-assertions/dispatch/tree/main/data/input-to-publish), and the JSON schemas for the specified input formats are descibed below: [TODO]

#### publish

*Description*

    publish a DAMF object starting from a dispatch standard input.

*Usage*

Run `dispatch publish <input-path> <target>` to publish a DAMF object starting from a dispatch standard input (a `json` file with path `<input-path`>). The `<target>` argument can take one of two values: `local` for local IPFS node pinning, or `cloud` for pinning through [web3.storage][w3s] service.

:warning: When `cloud` is used, make sure to have set your API token first, as described in the [set-web3token](#set-web3token) command section.

:warning: For publishing *assertion* objects, make sure to have the *agent* specified in the input `json` initially created, as described in the [create-agent](#create-agent) command section. Same applies in case a *profile name* is used for the *language* (using [create-language](#create-language)) and *tool* (using [create-tool](#create-tool)) fields instead of a direct `damf:cid`.

[w3s]: https://web3.storage

### Retrieval

#### Output formats

For the same reasons **Dispatch** reads standard inputs from producers, it constructs standard outputs for consumers. The output formats have the same structure as the input formats, where *local names* used in input formats as references to other objects in the file are replaced by the *global names* of these objects.

Examples of these formats can be found at the [dispatch github repository](https://github.com/distributed-assertions/dispatch/tree/main/data/output-from-get), and the JSON schemas are ...

#### get

*Description*

    retrieve a DAMF object by its cid.

*Usage*

Run `dispatch get <cid> <directory-path>` to retrieve a DAMF object starting from its `cid` and construct the corresponding standard output which contains the full DAG. `<directory-path>` refers to the container directory for the resulting output file.

:warning: Make sure that the gateway is set as described in the [set-gateway](#set-gateway) command section.

:information_source: Note that if the `ipfs daemon` is deactivated, the retrieval process will be successful in case the full DAG is present locally (if it was previously retrieved for example). If there were missing links, the gateway will be used. If the `ipfs daemon` is activated, the gateway will be used if the local daemon fails to retrieve the full DAG within [TODO] a specified time range.

### Trust Analysis

#### lookup

*Description*

*Usage*

## Ongoing developments
