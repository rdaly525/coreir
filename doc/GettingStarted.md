# Getting Started
This guide is meant to be a gentle introduction into the CoreIR API. You will build up a Module and a Generator from scratch.

`>cd tutorial/hellocounter`

## HelloModule

Open `hellomodule.cpp`
This file has a simple program that will construct a counter module.

```
>make build/hellomodule
>./build/hellomodule
```

## HelloModule Deep Dive

Open `hellomodule_desugar.cpp`.
Go through the code step by step. This should be a gentle introduce you to creating types, creating modules, instantiating Modules/Generators, and connecting things together. To compile simply do:

```
>make build/hellomodule_deep_dive
>./build/hellomodule_deep_dive
```
You should be able to see the pretty-printed version of the counter module you just created

You should see similar output to the previous example. 

## HelloModule Deep Dive

Open `hellomodule_deeper_dive.cpp`.
Go through the code step by step. This should have a complete description of most of the IR concepts and does not 'sugar' anything.

```
>make build/hellomodule_deeper_dive
>./build/hellomodule_deeper_dive
```

You should see similar output to the previous example. 

## HelloGenerator

Open `\hellogenerator.cpp`

Go through the code line by line. This should teach how to define parameters for generators, Define TypeGen, Functions for generating Types, Getting Values from args, creating Generator functions, running generators, casting, and more.
