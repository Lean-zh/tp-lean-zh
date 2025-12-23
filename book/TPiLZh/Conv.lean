import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiLZh

#doc (Manual) "转换策略模式" =>
%%%
file := "Conv"
tag := "conv"
%%%
-- The Conversion Tactic Mode

-- Inside a tactic block, one can use the keyword {tactic}`conv` to enter
-- _conversion mode_. This mode allows to travel inside assumptions and
-- goals, even inside function abstractions and dependent arrows, to apply rewriting or
-- simplifying steps.

在策略块中，可以使用关键字 {tactic}`conv` 进入 _转换模式_。这种模式允许在假设和目标内部，甚至在函数抽象和依赖箭头内部移动，以应用重写或简化步骤。

-- # Basic navigation and rewriting
# 基本导航和重写
%%%
tag := "basic-navigation-and-rewriting"
%%%

:::leanFirst
-- As a first example, let us prove example
-- {leanRef}`(a b c : Nat) : a * (b * c) = a * (c * b)`
-- (examples in this file are somewhat artificial since
-- other tactics could finish them immediately). The naive
-- first attempt is to enter tactic mode and try {leanRef}`rw [Nat.mul_comm]`. But this
-- transforms the goal into {leanRef}`b * c * a = a * (c * b)`, after commuting the
-- very first multiplication appearing in the term. There are several
-- ways to fix this issue, and one way is to use a more precise tool:
-- the conversion mode. The following code block shows the current target
-- after each line.

作为第一个例子，让我们证明 {leanRef}`(a b c : Nat) : a * (b * c) = a * (c * b)`（本段中的例子有些刻意设计，因为其他策略可以立即完成它们）。首次简单的尝试是进入策略模式并尝试 {leanRef}`rw [Nat.mul_comm]`。但这将目标转化为 {leanRef}`b * c * a = a * (c * b)`，因为它作用于项中出现的第一个乘法。有几种方法可以解决这个问题，其中一个方法是使用更精确的工具：转换模式。下面的代码块显示了每行之后的当前目标。

```lean (showProofStates := "oops conv1 conv2 conv3 conv4")
#guard_msgs (drop all) in
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm]
  -- ^ PROOF_STATE: oops

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
--  ^ PROOF_STATE: conv1
    lhs
--  ^ PROOF_STATE: conv2
    congr
--  ^ PROOF_STATE: conv3
    rfl
--  ^ PROOF_STATE: conv4
    rw [Nat.mul_comm]
```

:::

-- The above snippet shows three navigation commands:
--
-- - {leanRef}`lhs` navigates to the left-hand side of a relation (equality, in this case).
--    There is also a {tactic}`rhs` to navigate to the right-hand side.
-- - {leanRef}`congr` creates as many targets as there are (nondependent and explicit) arguments to the current head function
--   (here the head function is multiplication).
-- - {leanRef}`rfl` closes target using reflexivity.

上面这段涉及三个导航指令：

- {leanRef}`lhs` 导航到关系（此处是等式）左边。同理 {tactic}`rhs` 导航到右边。
- {leanRef}`congr` 创建与当前头函数的（非依赖的和显式的）参数数量一样多的目标（此处的头函数是乘法）。
- {leanRef}`rfl` 使用自反性关闭目标。

-- Once arrived at the relevant target, we can use {leanRef}`rw` as in normal
-- tactic mode.

一旦到达相关目标，我们就可以像在普通策略模式中一样使用 {leanRef}`rw`。

:::leanFirst
-- The second main reason to use conversion mode is to rewrite under
-- binders. Suppose we want to prove example
-- {leanRef}`(fun x : Nat => 0 + x) = (fun x => x)`.
-- The naive first attempt is to enter tactic mode and try
-- {leanRef}`rw [Nat.zero_add]`. But this fails with a frustrating

使用转换模式的第二个主要原因是在约束器下重写。假设我们想证明 {leanRef}`(fun x : Nat => 0 + x) = (fun x => x)`。首次简单的尝试是进入策略模式并尝试 {leanRef}`rw [Nat.zero_add]`。但这会失败并报错：

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

-- The solution is:

解决方案为：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) :=  by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```
:::

-- where {leanRef}`intro x` is the navigation command entering inside the {kw}`fun` binder.
-- Note that this example is somewhat artificial, one could also do:

其中 {leanRef}`intro x` 是导航命令，它进入了 {kw}`fun` 约束器。这个例子有点刻意，你也可以这样做：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

-- or just

或者这样：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

-- {leanRef}`conv` can also rewrite a hypothesis {lit}`h` from the local context, using {kw}`conv at`{lit}` h`.

{leanRef}`conv` 也可以用 {kw}`conv at`{lit}` h` 从局部上下文重写一个假设 {lit}`h`。

-- # Pattern matching
# 模式匹配
%%%
tag := "pattern-matching-conv"
%%%

-- Navigation using the above commands can be tedious. One can shortcut it using pattern matching as follows:

使用上面的命令进行导航可能很繁琐。可以使用下面的模式匹配来简化它：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]
```

-- which is just syntax sugar for

这是下面代码的语法糖：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

-- Of course, wildcards are allowed:

当然也可以用通配符：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

-- # Structuring conversion tactics
# 结构化转换策略
%%%
tag := "structuring-conversion-tactics"
%%%

-- Curly brackets and {lit}`.` can also be used in {leanRef}`conv` mode to structure tactics:

大括号和 {lit}`.` 也可以在 {leanRef}`conv` 模式下用于结构化策略：

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

-- # Other tactics inside conversion mode
# 转换模式中的其他策略
%%%
tag := "other-tactics-inside-conversion-mode"
%%%

-- - :::leanFirst
--   {leanRef}`arg`{lit}` i` enter the {lit}`i`-th nondependent explicit argument of an application.

- :::leanFirst
  {leanRef}`arg`{lit}` i` 进入一个应用的第 {lit}`i` 个非依赖显式参数。

  ```lean (showProofStates := "arg2 arg3")
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv =>
    -- ^ PROOF_STATE: arg1
      lhs
    -- ^ PROOF_STATE: arg2
      arg 2
    -- ^ PROOF_STATE: arg3
      rw [Nat.mul_comm]
  ```
  :::

-- - {tactic}`args` is an alternative name for {leanRef}`congr`.

- {tactic}`args` 是 {leanRef}`congr` 的替代名称。

-- -   {leanRef}`simp` applies the simplifier to the current goal. It supports the same options available in regular tactic mode.

-   {leanRef}`simp` 将简化器应用于当前目标。它支持常规策略模式中的相同选项。

    ```lean
    def f (x : Nat) :=
      if x > 0 then x + 1 else x + 2

    example (g : Nat → Nat)
        (h₁ : g x = x + 1) (h₂ : x > 0) :
        g x = f x := by
      conv =>
        rhs
        simp [f, h₂]
      exact h₁
    ```

-- - {kw}`enter`{lit}` [1, x, 2, y]` iterate {leanRef}`arg` and {leanRef}`intro` with the given arguments.

- {kw}`enter`{lit}` [1, x, 2, y]` 使用给定参数迭代 {leanRef}`arg` 和 {leanRef}`intro`。

-- - {tactic}`done` fail if there are unsolved goals.

- {tactic}`done` 如果有未解决的目标则失败。

-- - {tactic}`trace_state` display the current tactic state.

- {tactic}`trace_state` 显示当前策略状态。

-- - {tactic}`whnf` put term in weak head normal form.

- {tactic}`whnf` 将项置于弱首范式（weak head normal form）。

-- - {kw}`tactic`{lit}` => <tactic sequence>` go back to regular tactic mode. This
--   is useful for discharging goals not supported by {leanRef}`conv` mode, and
--   applying custom congruence and extensionality lemmas.

- {kw}`tactic`{lit}` => <tactic sequence>` 回到常规策略模式。这对于解决 {leanRef}`conv` 模式不支持的目标，以及应用自定义的一致性和扩展性引理很有用。

  ```lean (showProofStates := "convTac1 convTac2 convTac4")
  example (g : Nat → Nat → Nat)
          (h₁ : ∀ x, x ≠ 0 → g x x = 1)
          (h₂ : x ≠ 0)
          : g x x + x = 1 + x := by
    conv =>
      lhs
  --  ^    PROOF_STATE: convTac1
      arg 1
  --  ^    PROOF_STATE: convTac2
      rw [h₁]
      . skip
      . tactic =>
    --  ^    PROOF_STATE: convTac4
         exact h₂
  ```

-- - {kw}`apply`{lit}` <term>` is syntax sugar for {kw}`tactic`{lit}` => apply <term>`.

- {kw}`apply`{lit}` <term>` 是 {kw}`tactic`{lit}` => apply <term>` 的语法糖。

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
