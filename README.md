# Example TLA+ Specification For Leader Election

This repository contains an example [TLA+](https://github.com/tlaplus/tlaplus) specification for a simple "raft style" leader election protocol. This specification can be model checked both using TLC and [Apalache](https://github.com/informalsystems/apalache).

### Checking with TLC
TLC is the default model checker for [TLA+](https://github.com/tlaplus/tlaplus). Install instructions can be found [here](http://lamport.azurewebsites.net/tla/toolbox.html). I suggest either using the [VSCode plugin](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) or the command line interface (install script [here](https://github.com/pmer/tla-bin)).
The script can be checked as follows: 

```
$ tlc RaftLeader.tla
```

### Checking with Apalache
Apalache is a symbolic model checker for TLA+. Install instructions can be found [here](https://github.com/informalsystems/apalache). You can inductively check this spec as follows:

For the base case:
```
$ apalache-mc check --init=Init --inv=Inv --length=0 RaftLeader.tla
```

For the inductive case:
```
$ apalache-mc check --init=Inv --inv=Inv --length=1 RaftLeader.tla 
```