# Directions for overriding the C libraries

## FLINT

In `.julia/artifacts` you should have or make a file `Overrides.toml` with the
following entry (replace `/usr/local` with the location of your installation)

```
[e134572f-a0d5-539d-bddf-3cad8db41a82]
FLINT = "/usr/local"
```

The UUID is that of `FLINT_jll`, which is available in Nemo's `Project.toml`.
Note the case sensitivity of the artifact name: if the jll is called `XxX_jll`,
the entry should be `XxX = `. This is all that is needed to override the FLINT
location. If it has worked:

```
julia> using Nemo
julia> Nemo.libflint
"/usr/local/lib/libflint.so"
```

Troubleshooting guide:

- If setting up the override for the first time, Nemo should be re-precompiled.
  This can be triggered by touching a source file.

- Several of the other libraries depending on FLINT might want a specific
  so-version of FLINT. This can be tweaked by hacking the FLINT makefile.

## Arb

For Arb, adapt the following entry for `Overrides.toml`:

```
[d9960996-1013-53c9-9ba4-74a4155039c3]
Arb = "/usr/local"
```

## Antic

For Antic, adapt the following entry for `Overrides.toml`:

```
[e21ec000-9f72-519e-ba6d-10061e575a27]
Antic = "/usr/local"
```

## Calcium

For Calcium, adapt the following entry for `Overrides.toml`:

```
[fcfa6d1b-d8ce-59d5-8c0a-c0d7f69e4f40]
Calcium = "/usr/local"
```
