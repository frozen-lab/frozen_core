# FrozenCore

Custom implementations and core utilities for frozen codebases.

## Index

- [`ff`](#frozenfile)
- [`fm`](#frozenmmap)
- [`fe`](#frozenerror)
- [`hints`](#hints)
- [`notes`](#notes)

## FrozenFile

`FF` is a custom implementation of `std::fs::File`.

To use the `ff` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.2", features = ["ff"] }
```

`FF` is currently available for following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ❌      |
| `x86_64-apple-darwin`                 | ❌      |

For Example usage, refer to [example](./examples/ff_example.rs)

## FrozenMMap

`FM` is a custom implementation of `mmap`.

To use the `fm` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.2", features = ["fm"] }
```

`FM` is currently available for following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ❌      |
| `x86_64-apple-darwin`                 | ❌      |

For Example usage, refer to [example](./examples/fm_example.rs)

## FrozenError

`FRes` & `FErr` are custom implementation's for result and error propogation.

The `fe` module is available by deafult. Add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = "0.0.2"
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

The `hints` module is available by deafult. Add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = "0.0.2"
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you asume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
