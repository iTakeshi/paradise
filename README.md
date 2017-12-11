Macro paradise works with scalameta-v2
=======================================

[read original README](https://github.com/iTakeshi/paradise/blob/scalameta_v2/README.original.md)

### IMPORTANT NOTICE
I'm strongly recommend you NOT TO USE THIS REPOSITORY unless you are awere about what you are doing.
__Shipped with absolutely NO GUARANTEE. Use on YOUR OWN RESPONSIBILITY.__

### Introduction
Since scalameta v2.0 was released, [scalameta/paradise](https://github.com/scalameta/paradise) was abandoned.
Thus, we have to continue using scalameta v1 if we use scalameta-based macro system.
However, some graceful features of scalameta (such as improved semantic-db integration, etc.) are only supported by scalameta v2.
This repository is created for those who want to use scalameta-based macro system with scalameta v2.

### How to use
In your `build.sbt`,
```scala
resolvers += Resolver.bintrayRepo("itakeshi", "maven"),
libraryDependencies += "org.scalameta" %% "scalameta" % "2.1.3-32-bc734dc0-20171211-2240" // required to bring `inline` back with scalameta
addCompilerPlugin("org.scalameta" %% "paradise" % "3.0.0-324-eefdb72a.1512909854385" cross CrossVersion.full)
```

For brief review of AST, read a [note](https://github.com/scalameta/scalameta/blob/v2.1.3/notes/quasiquotes.md)

### Acknowledgments
I would like to appreciate @xeno-by and scalameta developers team for their great products.
