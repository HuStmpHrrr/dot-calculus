Extensions for Dependent Object Types (DOT)
-------------------------------------------

This is a fork of the [Wadlerfest DOT](http://infoscience.epfl.ch/record/215280/files/paper_1.pdf) [type soundness proof](https://github.com/samuelgruetter/dot-calculus).

It provides extensions of the [original proof](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/dot_top_bot.v) with 
- mutation
  ([proof](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/mutation/dot_top_bot_mut.v) | [technical report](https://arxiv.org/abs/1611.07610) | [documentation](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/mutation/README.md))
- expanded type paths
  ([proof](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/paths/dot_top_bot_path.v) | [description](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/paths/README.md)).

We are also working on [simplifying](https://github.com/amaurremi/dot-calculus/blob/master/dev/lf/good-proof) the original proof by changing the definition of possible types.
