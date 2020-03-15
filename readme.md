# desert

traits for {de,ser}ializing compact binary formats

* compact representations for the builtin container types (tuples, arrays,
  slices, vectors) is provided.
* varint length encoding scheme for slices and vectors (1 byte for len < 128)
* emphasis on ergonomics of implementing custom binary {de,ser}ializers

This crate does not (presently) provide automatic derivation. Instead, the
emphasis is on having a good collection of compact implementations for built-in
containers and making it easy to implement your own binary formats manually.

# rationale

Rust core has some useful methods defined on builtin types:
`5000u32.to_be_bytes()`, `u32::from_be_bytes([u8;4])`, etc.

These methods are certainly useful, but they belong to the builtin types, not
traits. This makes it difficult to write a generic interface that accepts
anything that can be serialized to bytes.

Other options such as serde with bincode let you derive custom implementations
of Serialize and Derive, which are very convenient and you can support for many
other output formats besides binary. However, if you want implement your own
custom serialization and especially deserialization, things get very difficult.
For deserialization you need to implement a Visitor and things get very messy
quickly.

bincode also makes trade-offs that make sense for quickly marshalling data into
and out of memory with minimal parsing overhead, but this choice means that
things like vectors get `usize` bytes padded to the beginning which is 8 whole
bytes on a 64-bit machine and enums under the automatic derivation will always
be prefaced with a `u32` even if there are only 2 options to enumerate. These
trade-offs are not ideal for situations where you need more fine-grained control
over the representation of your structs at a byte-level to keep overhead low or
to integrate with an existing externally-defined wire-protocol. But to achieve
those custom byte formats with serde and bincode, you would need to implement
very generic and difficult serde interfaces when you might only care about bytes
over the wire or on disk.

Another common issue working with binary data is reading large chunks from the
network or from disk in sizes determined by the network transport or physical
medium. Those sizes are very unlikely to map nicely to your data structures, so
it is very useful to be able to count (without parsing into a new instance) how
many bytes can be read from a `[u8]` slice to arrive at the ending byte offset
for the particular data structure under consideration which may have a dynamic
size. Or it may also be helpful to know when the data structure's representation
extends past the end of the buffer slice and the program should fetch more data
from the network or from on disk. These concerns are provided by the
`CountBytes` traits.

