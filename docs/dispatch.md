# Dispatch: Join the DAMF with ease

**Dispatch** is an Intermediary tool for publishing, retrieval, and trust analysis in the Distributed Assertion Management Framework (DAMF).

It is based on the [DAMF Formats](./damf-formats.md) specification and implements the main [DAMF processes](./damf-processes.md). It is intended to be usable by both human users and tools.

## Obtaining and Building

### Source

- [Zip][dispatch-zip]
- [Github][dispatch-repo]

[dispatch-zip]: assets/zips/dispatch-b778c71dc35c6c1ae05d2cd4853d648659562cfe.zip
[dispatch-repo]: https://github.com/distributed-assertions/dispatch/tree/b778c71dc35c6c1ae05d2cd4853d648659562cfe

### Requirements

- [`Kubo`][kubo] - previously known as `ipfs-go`. The tested version is `ipfs version 0.28.0`.
- [`nodejs`][nodejs]. The tested version is `v18.12.1`.

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

#### set-w3-email & set-w3-space

*Description*

    - set-w3-email: setup a web3.storage account email.
    - set-w3-space: setup a web3.storage account space key.

*Usage*

**Dispatch** initially publishes objects through the local IPFS daemon, and pins them *locally* on the local IPFS node. This means that initial requests to get a `cid` will have to retrieve it from the publisher's local IPFS node, which could be a bit slow at the beginning. In order to make the retrieval process faster, **Dispatch** allows the use of the [web3.storage](https://web3.storage) service as a *pinning service* that serves in making published objects more easily discoverable through the IPFS network.

In the current dispatch implementation, the way of using of this service is expected as follows:

1. Create a [web3.storage account](https://web3.storage/login/) and a [space](https://web3.storage/docs/how-to/create-space/) to upload data within. More details on this can be found at the [web3.storage website](https://web3.storage/). In the current implementation of dispatch, the usage of this service is still experimental and provides the very basic functionality. More can be done and said in future steps.

2. Run `dispatch set-w3-email <email>` to set your account's email as a *login* email to be used in later steps by `dispatch`. Note that you will need to verify your email address after the login attempt by `dispatch`, when you try to [publish](#publish) data using this service. More details can be found in the [official documentation](https://web3.storage/docs/w3up-client/).

3. Run `dispatch set-w3-space <space>` with the generated space key as an argument to be used in later steps by `dispatch`: as the space to upload your data within.

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

As illustrated in [DAMF Formats](./damf-formats.md), the *global shared objects* shall follow the specified DAMF formats: *assertion*, *production*, *sequent*, *formula*, etc.

**Dispatch** provides an *interface* for users (human users or tools) to the DAMF store through a collection of standard input formats. These standard inputs are produced by users, then processed and published by *Dispatch* as DAMF objects. In this way, a user does not have to interact with IPFS in any form.

Examples of these formats can be found in the [dispatch github repository](https://github.com/distributed-assertions/dispatch/tree/b778c71dc35c6c1ae05d2cd4853d648659562cfe/data/input-to-publish/formats). (Similarly found in the `/data/input-to-publish/formats/` directory within the associated [dispatch Zip](#source)).

#### publish

*Description*

    publish a DAMF object starting from a dispatch standard input.

*Usage*

Run `dispatch publish <input-path> <target>` to publish a DAMF object starting from a dispatch standard input (a `json` file with path `<input-path>`). The `<target>` argument can take one of two values: `local` for local IPFS node pinning, or `cloud` for pinning through [web3.storage][w3s] service.

:warning: When `cloud` is used, make sure to have set your web3.storage account's email and space first, as described in the [set-w3-email & set-w3-space](#set-w3-email-set-w3-space) commands section.

:warning: For publishing *assertion* objects, make sure to have the *agent* specified in the input `json` initially created, as described in the [create-agent](#create-agent) command section. Same applies in case a *profile name* is used for the *language* (using [create-language](#create-language)) and *tool* (using [create-tool](#create-tool)) fields instead of a direct `damf:cid`.

[w3s]: https://web3.storage

### Retrieval

#### Output formats

For the same reasons **Dispatch** reads standard inputs from producers, it constructs standard outputs for consumers. The output formats have the same structure as the input formats, where *local names* used in input formats as references to other objects in the file are replaced by the *global names* of these objects.

Examples of these formats can be found at the [dispatch github repository](https://github.com/distributed-assertions/dispatch/tree/b778c71dc35c6c1ae05d2cd4853d648659562cfe/data/output-from-get/formats).
(Similarly found in the `/data/output-from-get/formats/` directory within the associated [dispatch Zip](#source)).

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

    construct all trust paths for a formula cid in a list of assertions 

*Usage*

This command is the starting point for DAMF trust analysis in **Dispatch**. Run `dispatch lookup <formula-cid> <assertion-list> <directory-path>` to get all the possible trust paths that lead to this formula.

`<formula-cid>` is the `cid` of the target *formula object*.

`<assertion-list>` is the path of the file containing the list of *assertion object* `cids` to search through.
For example:

   ~~~~js
   [
     "bafyreigqz7mw5bol3xi5qrwioseujh4fkufl5j6i4pxtl2fsynisi4zix4",
     "bafyreiea2oi25iw4des2c7yp56kcouleoy7uri5gnolunedfygzb77xkdi"
   ]
   ~~~~

`<directory-path>` refers to the container directory for the resulting output file.

A trust path is of the form:

   ~~~~js
   {
     "dependencies": [cid-formula],
     "via": [{agent, mode}]
   }
   ~~~~

An example would be:

   ~~~~js
   {
     "dependencies": [cidA, cidB],
     "via": [{K1, T1}, {K4, T6}]
   }
   ~~~~

The above example trust path would be interpreted as: *The target formula can be reached **via trusting** `[{K1, T1}, {K4, T6}]`, with the formulas `[cidA, cidB]` as remaining dependencies*.

## Ongoing developments
