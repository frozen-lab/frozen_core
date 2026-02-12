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

| Platform                    | Support |
| --------------------------- |:-------:|
| `x86_64-unknown-linux-gnu`  | ✅      |
| `aarch64-unknown-linux-gnu` | ✅      |
| `x86_64-apple-darwin`       | ❌      |
| `aarch64-apple-darwin`      | ❌      |
| `x86_64-pc-windows-msvc`    | ❌      |

Example usage,

```rs
use frozen_core::ff::{FF, FFCfg};

const MODULE_ID: u8 = 1;

fn main() {
    let path = "/tmp/example/data.bin".into();
    let ff = FF::new(FFCfg::new(path, MODULE_ID), 16).expect("create");

    let data = 42u64.to_le_bytes();
    ff.write(data.as_ptr(), 0, data.len()).expect("write");
    ff.sync().expect("sync");

    let mut buf = [0u8; 8];
    ff.read(buf.as_mut_ptr(), 0, buf.len()).expect("read");

    assert_eq!(u64::from_le_bytes(buf), 42);
}
```

## FrozenMMap

`FM` is a custom implementation of `mmap`.

To use the `fm` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.2", features = ["fm"] }
```

`FM` is currently available for following platforms,

| Platform                    | Support |
| --------------------------- |:-------:|
| `x86_64-unknown-linux-gnu`  | ✅      |
| `aarch64-unknown-linux-gnu` | ✅      |
| `x86_64-apple-darwin`       | ❌      |
| `aarch64-apple-darwin`      | ❌      |
| `x86_64-pc-windows-msvc`    | ❌      |

Example usage,

```rs
use frozen_core::fm::{FM, FMCfg};
use frozen_core::ff::{FF, FFCfg};

const MODULE_ID: u8 = 1;

fn main() {
    let path = "/tmp/example/data.bin".into();
    let ff = FF::new(FFCfg::new(path, MODULE_ID), 8).expect("file");
    let fm = FM::new(ff.fd(), 8, FMCfg::new(MODULE_ID)).expect("mmap");

    {
        let w = fm.writer::<u64>(0).expect("writer");
        w.write(|v| *v = 0xDEADBEEF).expect("write");
    }

    fm.sync().expect("sync");

    let r = fm.reader::<u64>(0).expect("reader");
    let value = r.read(|v| *v);

    assert_eq!(value, 0xDEADBEEF);
}
```

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

Example usage,

```rs
use frozen_core::hints::{likely, unlikely};

fn main() {
    let enabled = true;
    let values = [1, 2, 3, -1, 4];

    // Hot configuration path
    if likely(enabled) {
        fast_path();
    }

    // Hot loop with rare error case
    for v in values {
        if unlikely(v < 0) {
            continue; // rare invalid value
        }
        process(v);
    }
}

#[inline]
fn fast_path() {
    // expected fast path
}

#[inline]
fn process(_v: i32) {
    // normal processing
}
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you asume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
