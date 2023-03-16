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

Calling `dispatch` will list the available commands:

### Configuration

#### create-agent

*Description*

    create an agent profile with a public-private key pair.

*Usage*

#### create-tool

*Description*

    create a tool profile from a new description or from an existing tool cid.

#### create-language

*Description*

    create a language profile from a new description or from an existing language cid.

*Usage*

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
