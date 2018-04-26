# Getting Started
This guide is meant to be a gentle introduction into the CoreIR API. You will build up a Module and a Generator from scratch.

If you have not built coreir yet, please follow the INSTALL.md guide.

`>cd tutorial/hellocounter`

## HelloModule

There are three files here. the vanilla module creation, the deep dive and the deeper dive. It is easiest to look at the files in that order. 

Open `hellomodule.cpp`
This file has a simple program that will construct a counter module.

```
>make build/hellomodule
>./build/hellomodule
```

## HelloModule Deep Dive

Open `hellomodule_deep_dive.cpp`.
Go through the code step by step. This should be a gentle introduce you to creating types, creating modules, instantiating Modules/Generators, and connecting things together. To compile simply do:

```
>make build/hellomodule_deep_dive
>./build/hellomodule_deep_dive
```
You should be able to see the pretty-printed version of the counter module you just created

You should see similar output to the previous example. 

## HelloModule Deeper Dive

Open `hellomodule_deeper_dive.cpp`.
Go through the code step by step. This should have a complete description of most of the IR concepts and does not 'sugar' anything.

```
>make build/hellomodule_deeper_dive
>./build/hellomodule_deeper_dive
```

You should see similar output to the previous example. 

## HelloGenerator

There are two files here. The vanilla generator creation, and the deep dive for generators. Again, it is best to look at the files in that order. 
Open `\hellogenerator.cpp`

This file has a simple program to define and use a counter generator.

```
>make build/hellogenerator
>./build/hellogenerator
```



## HelloGenerator Deep Dive

This file goes through a lot more of the generator-related IR/API.

```
>make build/hellogenerator_deep_dive
>./build/hellogenerator_deep_dive
```


