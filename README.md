# FrozenCore

Custom implementations and core utilities for frozen codebases.

## Index

- [`setup`](#setup)
- [`ffile`](#frozenfile)
- [`fmmap`](#frozenmmap)
- [`error`](#frozenerr)
- [`hints`](#hints)
- [`notes`](#notes)

## Setup

Add following to your `Cargo.toml`,

```toml
[dependencies]
frozen-core = { version = "0.0", default-features = true }
```

> [!TIP]
> All the features available by default. To disable this, set `default-features = false`

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0", default-features = false, features = ["ffile"] }
```

`FrozenFile` is currently available on the following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

For example usage, refer to [example](./examples/ff.rs)

## FrozenMMap

`FrozenMMap` is a custom implementation of `mmap`.

To use the `fmmap` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0", default-features = false, features = ["fmmap"] }
```

`FrozenMMap` is currently available on the following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

For example usage, refer to [example](./examples/fm.rs)

## FrozenErr

`FRes` & `FErr` are custom implementation's for result and error propogation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0", default-features = false, features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0", default-features = false, features = ["hints"] }
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you asume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
