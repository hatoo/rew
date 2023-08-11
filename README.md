# rew

`rew` is a simple math formula rewriter using [egg](https://github.com/egraphs-good/egg).

Formulae are represented as S-expressions.

# Examples

```
$ rew '(+ 1 2)'
3
```

```
$ rew '(+ x (+ x (+ x 6)))'
(+ 6 (* x 3))
```