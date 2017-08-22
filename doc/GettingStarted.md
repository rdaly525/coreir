# Getting Started
This guide is meant to be a gentle introduction into the CoreIR API. You will build up a Module and a Generator from scratch. First do:

`>cd tutorial/hellocounter`

## HelloModule

Open `hellomodule.cpp`.
Go through the code step by step. This should introduce you to creating types, creating modules, instantiating Modules/Generators, and connecting things together. To compile simply do:

```
>make build/hellomodule
>./build/hellomodule
```

You should be able to see the pretty-printed version of the counter module you just created

## HelloModuleSugar

Open `hellomodulesugar.cpp`

Now go through this code line by line. This is creating the exact same module as before but in a more succinct way (hence the syntax sugar). Compile this by doing:

```
>make build/hellomodulesugar
>./build/hellomodulesugar
```

You should see similar output to the previous example. 

## HelloGenerator

Open `\hellogenerator.cpp`

Go through the code line by line. This should teach how to define parameters for generators, Define TypeGen, Functions for generating Types, Getting Values from args, creating Generator functions, running generators, casting, and more.