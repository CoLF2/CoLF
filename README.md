Install Deps:

```
opam install . --deps-only
```

Build:

```
dune build
```

Exec:

```
rlwrap dune exec -- lftest08 elftest2/param_subtype.colf
```



## v2 of recursive definitions

I think I want to ensure that everthing should be writte in the beta-normal eta-long form, without implicit arguments. For example, if {x : A -> B}, occurrences of x should be written as ([y] x y).

We allow recursive definitions of the following form:

```
a1 : K1.
...
an : Kn.
c1 : A1.
...
cn : An.

r1 : A1 = M1.
r2 : A2 = M2.
...
rn : An = Mn.

d1 : B1.
...
```

In particular in the set of recursive definitions, A1...An cannot mention r1...rn. M1...Mn, may mention r1...rn. B1 may mention r1...rn.


## VSCode Extension


The `vscode-colf` contains a vscode extension for CoLF. To build it, run the following commands inside the `vscode-colf` directory:

```
npm install
vsce package
```

To install a vsix file, press `Ctrl+Shift+P` and select `Extensions: Install from VSIX...` and select the generated vsix file.

You need to configure the CoLF interpreter path in the settings. Press `Ctrl+,` and search for `Colf-server-path`. Set the path to the CoLF interpreter binary, which is located at `<pwd>/_build/install/default/bin/lftest08`, use absolute path.


Edit any file with `.colf` extension and you should get feedbacks upon saving the file.


