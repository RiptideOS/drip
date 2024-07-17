# The Drip Programming Language

A compiled systems programming language tailored for operating system development.

The bootstrap compiler is currently in development and is written in Rust.

## Fundamental Types

| Name             | Syntax                           | Size (bytes)                | Description                                                                       |
| ---------------- | -------------------------------- | --------------------------- | --------------------------------------------------------------------------------- |
| Primitive        | `u8` \| `char`                   | 0-8                         | Basic data types                                                                  |
| Pointer          | `*u8`                            | Platform Pointer Width      | Raw pointer to a type                                                             |
| Slice            | `[u8]` \| `[str]`                | 2 \* Platform Pointer Width | A fat pointer to a type which stores the pointer and the length                   |
| String Slice     | `str`                            | 2 \* Platform Pointer Width | A fat pointer to some UTF-8 encoded bytes which stores the pointer and the length |
| C String         | `cstr`                           | Platform Pointer Width      | A raw pointer to a `null` (`\0`) terminated C style string                        |
| Array            | `[u8; N]`                        | N \* sizeof(T)              | A contiguous memory region storing N elements of a type                           |
| Function Pointer | `fn (i32, i32, ...[i32]) -> i32` | Platform Pointer Width      | A pointer to a function with some signature                                       |
| Any Pointer      | `*any`                           | Platform Pointer Width      | A raw pointer to any kind of data with an unknown size and length                 |

## Primitives

| Name    | Size (bytes)           | Description                              |
| ------- | ---------------------- | ---------------------------------------- |
| `()`    | 0                      | The unit type                            |
| `bool`  | 1                      | A boolean                                |
| `char`  | 4                      | 32-bit UTF-32 encoded unicode code point |
| `u8`    | 1                      | 8-bit unsigned integer                   |
| `u16`   | 2                      | 16-bit unsigned integer                  |
| `u32`   | 4                      | 32-bit unsigned integer                  |
| `u64`   | 8                      | 64-bit unsigned integer                  |
| `usize` | Platform Pointer Width | Platform sized unsigned integer          |
| `i8`    | 1                      | 8-bit signed integer                     |
| `i16`   | 2                      | 16-bit signed integer                    |
| `i32`   | 4                      | 32-bit signed integer                    |
| `i64`   | 8                      | 64-bit signed integer                    |
| `isize` | Platform Pointer Width | Platform sized signed integer            |
| `f32`   | 4                      | 32-bit floating point number             |
| `f64`   | 8                      | 64-bit floating point number             |
