# IsaPlanner - a Proof Planner for Isabelle

IsaPlanner is a proof planner for [Isabele](http://isabelle.in.tum.de/). It
facilitates the encoding of reasoning techniques and their application to prove
theorems in Isabelle. In particular, it provides an inductive prover based on
Rippling, as well as automatic theory formation tools (IsaCoSy and IsaScheme)

IsaPlanner is written in Isabelle/StandardML (based on
[PolyML](http://www.polyml.org/)

The old IsaPlanner homepage is here: http://dream.inf.ed.ac.uk/projects/isaplanner

See the INSTALL file for more information on how to install
IsaPlanner. (briefly, run the command "isabelle make" and you are
done)

You want to be familiar with [Isabele](http://isabelle.in.tum.de/) before trying
to use IsaPlanner. :)

This version of IsaPlanner is intended to work with Isabelle 2015 and requires that you have a clone/download of the [Isabelle-2015 branch of isaplib](https://github.com/iislucas/isaplib/tree/Isabelle-2015) in your Isabelle contrib directory.


## Quickly playing with IsaPlanner

Simply open the file `quicktest.thy` in Isabelle 2015.

## Setup IsaPlanner Heap

To use IsaPlanner, you should build the heap from IsaPlanner dir by running the command:

```
isabelle build -d . -b HOL-IsaPlannerSession
```

This will build and ML heap (also sometimes referred to as an Isabelle Session)
called "HOL-IsaPlannerSession" containing Isabelle/HOL with IsaPlanner tools loaded in a
theory "IsaP". Now you can make a new theory that imports "IsaP" and in that
theory you can use IsaPlanner and IsaCoSy.

For example, start Isabelle with the Isabelle session 'HOL-IsaPlannerSession' using this command:
```
isabelle jedit -l HOL-IsaPlannerSession -d ISAPLANNER_DIRECTORY
```

where `ISAPLANNER_DIRECTORY` is dierctory containing IsaPlanner (optionally relative to the current
directory).

## Developing new techniques

You'll be doing ML programming in Isabelle, so make sure to have the
[Isabelle CookBook](http://www.dcs.kcl.ac.uk/staff/urbanc/Cookbook/) handy.

TODO: complete this section. :)
