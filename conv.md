<!--
The Conversion Tactic Mode
=========================
-->

转换策略模式
=========================

<!--
Inside a tactic block, one can use the keyword `conv` to enter
conversion mode. This mode allows to travel inside assumptions and
goals, even inside function abstractions and dependent arrows, to apply rewriting or
simplifying steps.
-->

在策略块中，可以使用关键字`conv`进入转换模式(conversion mode)。这种模式允许在假设和目标内部，甚至在函数抽象和依赖箭头内部移动，以应用重写或简化步骤。

<!--
Basic navigation and rewriting
-------
-->

基本导航和重写
-------

<!--
As a first example, let us prove example
`(a b c : Nat) : a * (b * c) = a * (c * b)`
(examples in this file are somewhat artificial since
other tactics could finish them immediately). The naive
first attempt is to enter tactic mode and try `rw [Nat.mul_comm]`. But this
transforms the goal into `b * c * a = a * (c * b)`, after commuting the
very first multiplication appearing in the term. There are several
ways to fix this issue, and one way is to use a more precise tool:
the conversion mode. The following code block shows the current target
after each line.
-->

作为第一个例子，让我们证明`(a b c : Nat) : a * (b * c) = a * (c * b)`（本段中的例子有些刻意设计，因为其他策略可以立即完成它们）。首次简单的尝试是尝试`rw [Nat.mul_comm]`，但这将目标转化为`b * c * a = a * (c * b)`，因为它作用于项中出现的第一个乘法。有几种方法可以解决这个问题，其中一个方法是

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    rw [Nat.mul_comm b c]
```

不过本节介绍一个更精确的工具：转换模式。下面的代码块显示了每行之后的当前目标。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    congr
    -- 2 goals: ⊢ a, ⊢ b * c
    rfl
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

<!--
The above snippet shows three navigation commands:

- `lhs` navigates to the left hand side of a relation (here equality), there is also a `rhs` navigating to the right hand side.
- `congr` creates as many targets as there are (nondependent and explicit) arguments to the current head function
  (here the head function is multiplication).
- `rfl` closes target using reflexivity.

Once arrived at the relevant target, we can use `rw` as in normal
tactic mode.

The second main reason to use conversion mode is to rewrite under
binders. Suppose we want to prove example
`(fun x : Nat => 0 + x) = (fun x => x)`.
The naive first attempt is to enter tactic mode and try
`rw [Nat.zero_add]`. But this fails with a frustrating
-->

上面这段涉及三个导航指令：

- `lhs`（left hand side）导航到关系（此处是等式）左边。同理`rhs`导航到右边。
- `congr`创建与当前头函数的(非依赖的和显式的)参数数量一样多的目标（此处的头函数是乘法）。
- `skip`走到下一个目标。

一旦到达相关目标，我们就可以像在普通策略模式中一样使用`rw`。

使用转换模式的第二个主要原因是在约束器下重写。假设我们想证明`(fun x : Nat => 0 + x) = (fun x => x)`。首次简单的尝试`rw [zero_add]`是失败的。报错：

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

（错误：'rewrite'策略失败了，没有找到目标表达式中的模式0 + ?n）

<!--
The solution is:
-->

解决方案为：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

<!--
where `intro x` is the navigation command entering inside the `fun` binder.
Note that this example is somewhat artificial, one could also do:
-->

其中`intro x`是导航命令，它进入了`fun`约束器。这个例子有点刻意，你也可以这样做：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

<!--
or just
-->

或者这样：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

<!--
`conv` can also rewrite a hypothesis `h` from the local context, using `conv at h`.
-->

所有这些也可以用`conv at h`从局部上下文重写一个假设`h`。

<!--
Pattern matching
-------
-->

模式匹配
-------

<!--
Navigation using the above commands can be tedious. One can shortcut it using pattern matching as follows:
-->

使用上面的命令进行导航可能很无聊。使用下面的模式匹配来简化它：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
```

<!--
which is just syntax sugar for
-->

这是下面代码的语法糖：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

<!--
Of course, wildcards are allowed:
-->

当然也可以用通配符：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

<!--
Structuring conversion tactics
-------
-->

结构化转换策略
-------

<!--
Curly brackets and `.` can also be used in `conv` mode to structure tactics.
-->

大括号和`.`也可以在`conv`模式下用于结构化策略。

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

<!--
Other tactics inside conversion mode
----------
-->

转换模式中的其他策略
----------

<!--
- `arg i` enter the `i`-th nondependent explicit argument of an application.
-->

- `arg i`进入一个应用的第`i`个非独立显式参数。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    arg 2
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

<!--
- `args` alternative name for `congr`.

- `simp` applies the simplifier to the current goal. It supports the same options available in regular tactic mode.
-->

- `args`是`congr`的替代品。

- `simp`将简化器应用于当前目标。它支持常规策略模式中的相同选项。

```lean
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁
```

<!--
- `enter [1, x, 2, y]` iterate `arg` and `intro` with the given arguments. It is just the macro:
-->

- `enter [1, x, 2, y]`是`arg`和`intro`使用给定参数的宏。

```
syntax enterArg := ident <|> group("@"? num)
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i:num]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))
```

<!--
- `done` fail if there are unsolved goals.

- `trace_state` display the current tactic state.

- `whnf` put term in weak head normal form.

- `tactic => <tactic sequence>` go back to regular tactic mode. This
  is useful for discharging goals not supported by `conv` mode, and
  applying custom congruence and extensionality lemmas.
-->

- `done`会失败如果有未解决的目标。

- `traceState`显示当前策略状态。

- `whnf` put term in weak head normal form.

- `tactic => <tactic sequence>`回到常规策略模式。这对于退出`conv`模式不支持的目标，以及应用自定义的一致性和扩展性引理很有用。

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- ⊢ g x x + x
    arg 1
    -- ⊢ g x x
    rw [h₁]
    -- 2 goals: ⊢ 1, ⊢ x ≠ 0
    . skip
    . tactic => exact h₂
```

<!--
- `apply <term>` is syntax sugar for `tactic => apply <term>`
-->

- `apply <term>`是`tactic => apply <term>`的语法糖。

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
```
