# Writing Passes
Note: these tutorials will not currently compile as they are using an old API. Will be updated soon
This guide is meant to be an introduction into writing passes

`>cd tutorial/hellopasses`

## HelloNamespace

open up hellonamespace.cpp and read through the code line by line. This will teach you the basics of passes

To run this do:

```
>make build/hellonamespace so
> ./../../bin/coreir -i counters.json --load_passes build/hellonamespace.so -p hellonamespace
```
If you are on a mac, replace so with dylib

##HelloModule

Open hellomodule.hpp followed by hellomodule.cpp and read through the code line by line. This will tell you about writing
module passes.

```
>make build/hellomodule so
>./../../bin/coreir -i counters.json --load_passes build/hellomodule.so -p hellomodule
``` 
If you are on a mac, replace so with dylib

##HelloInstanceGraph

Open up helloinstancegraph.cpp and read through the code line by line. This will teach about pass dependencies, instance graphs, passthroughs, and more.

```
>make build/hellomodule so
>./../../bin/coreir -i counters.json --load_passes build/helloinstancegraph.so -p helloinstancegraph
``` 
If you are on a mac, replace so with dylib
