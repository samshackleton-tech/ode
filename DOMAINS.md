# Content identities bind meaning as well as bytes

Every Ode identity uses **BLAKE3 derive-key mode** with a caller-selected,
versioned semantic context. It commits to the object's bytes, its kind,
and the version of what those bytes mean. Identical bytes used as a
specification, proof, or instruction stream are hashed in different domains.
Cross-domain matches require a cryptographic collision.

`ode/domains.py` is the registry. A context has this exact form:

```
https://github.com/samshackleton-tech/ode/<kind>/semantics-v<revision>
```

The URL is a permanent namespace, not a runtime fetch location. A repository
move does not rename it. All current revisions are 1:

| Kind | Meaning committed by its domain |
|---|---|
| `spec` | Ode word/natural/list specification semantics |
| `certificate` | Executable verification claims and callee bindings |
| `theory` | Kernel sorted definitions and structural recursion |
| `goal` | Kernel universally quantified sorted equations |
| `proof` | Kernel equality and structural-induction derivations |
| `binary-w32` | W32 bytecode encoding and execution model |
| `binary-a64` | Supported AArch64 encoding and execution model |
| `package-file` | Exact bytes of one delivered package file |
| `package-tree` | Sorted path/NUL/file-identity manifest |

## The caller chooses the domain

`hash_of(value, kind)` hashes canonical s-expression bytes in the requested
current domain. It requires the kind; it does not infer meaning from an
untrusted object's tag. A store reader expecting a specification supplies
`spec`, then checks the object's type and content. Producers filing typed
objects may use the kind they are constructing.

`binary_hash(data, isa)` requires `w32` or `a64`. A certificate reader selects
the binary domain from the claimed execution model; substituting another
model invalidates the identity even when the bytes are unchanged.

The bootstrap hashes each file in `package-file` and the manifest in
`package-tree`. Its root includes the same registry and BLAKE3 implementation
as the toolchain, and serves both to delivered packages from memory.
`game/pin_ode_base.py` refreshes those shared root modules and both delivered
packages; owner semantic pins remain an explicit migration step.

## Changing meaning changes the domain

A change to the semantic contract requires a new revision for every affected
kind, **even when the serialized bytes and format version stay the same**.
Examples include changing specification operators, instruction interpretation,
proof-object meaning, or package-manifest interpretation. The owner of that
semantic change updates the registry, callers, dependent identities, generated
artifacts, and pins in the same change.

An Ode release with different specification semantics needs a different
`spec` context. A release with the same meaning can retain it. A format
number and a semantic revision are also distinct. Current kernel objects
serialize version 3 while their semantic domains are revision 1. A
meaning-preserving implementation refactor keeps the revision. Fixing an
implementation to meet its existing contract changes the delivered code pin;
it does not automatically change the contract's semantic revision.

Dependency identities are embedded in certificates, goals, proofs, and callee
references, so a changed semantic identity also changes its dependents. Readers
accept exactly the current domains. They do not try older domains or unkeyed
hashes as compatibility alternatives. Old identities are checked with the
tools and semantic domains of their original revision. Reusing identical
source bytes under a new domain creates a new identity.

## BLAKE3 mechanism and tests

`ode.blake3.derive_key(context, material)` implements standard derive-key mode:
the UTF-8 context is hashed with `DERIVE_KEY_CONTEXT`; the resulting 256-bit
key hashes the material with `DERIVE_KEY_MATERIAL`. These flags are also
carried through chunk and parent nodes. Contexts are public; this is domain
separation, not secret-key authentication. It is not a plain concatenation
of a label and the payload.

The unkeyed primitive remains for implementing/testing standard BLAKE3, whose
published outputs are unchanged. Ode identities never call it. Tests cover
all 35 official hash/derive-key vectors, including chunk/tree boundaries,
identical bytes across every domain, semantic revision changes without format
changes, model substitutions, and rejection of unkeyed/old-domain store names.
The tests also constrain imports of the raw primitive to standard-algorithm
and domain-separation tests.
