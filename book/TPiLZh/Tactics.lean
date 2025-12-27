import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Manual hiding tactic
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "证明策略" =>
%%%
tag := "tactics"
file := "Tactics"
%%%
-- Tactics

-- In this chapter, we describe an alternative approach to constructing
-- proofs, using _tactics_.  A proof term is a representation of a
-- mathematical proof; tactics are commands, or instructions, that
-- describe how to build such a proof. Informally, you might begin a
-- mathematical proof by saying “to prove the forward direction, unfold
-- the definition, apply the previous lemma, and simplify.” Just as these
-- are instructions that tell the reader how to find the relevant proof,
-- tactics are instructions that tell Lean how to construct a proof
-- term. They naturally support an incremental style of writing proofs,
-- in which you decompose a proof and work on goals one step at a time.

在本章中，我们描述了另一种构建证明的方法，即使用 _策略（Tactic）_ 。
一个证明项代表一个数学证明；策略是描述如何建立这样一个证明的命令或指令。
你可以在数学证明开始时非正式地说：“为了证明条件的必要性，展开定义，应用前面的定理，并进行简化。”
就像这些指令告诉读者如何构建证明一样，策略告诉 Lean 如何构建证明。
它们自然而然地支持增量式的证明书写，在这种写作方式中，你将分解一个证明，并一步步地实现目标。

-- We will describe proofs that consist of sequences of tactics as
-- “tactic-style” proofs, to contrast with the ways of writing proof
-- terms we have seen so far, which we will call “term-style”
-- proofs. Each style has its own advantages and disadvantages. For
-- example, tactic-style proofs can be harder to read, because they
-- require the reader to predict or guess the results of each
-- instruction. But they can also be shorter and easier to
-- write. Moreover, tactics offer a gateway to using Lean's automation,
-- since automated procedures are themselves tactics.

我们将把由策略序列组成的证明描述为“策略式”（tactic-style）证明，
前几章的证明我们称为“项式”（term-style）证明。每种风格都有自己的优点和缺点。
例如，策略式证明可能更难读，因为它们要求读者预测或猜测每条指令的结果。
但它们一般更短，更容易写。此外，策略提供了一个使用 Lean 自动化的途径，因为自动化程序本身就是策略。

-- # Entering Tactic Mode
# 进入策略模式
%%%
tag := "entering-tactic-mode"
%%%


:::leanFirst
-- Conceptually, stating a theorem or introducing a {kw}`have` statement
-- creates a goal, namely, the goal of constructing a term with the
-- expected type. For example, the following creates the goal of
-- constructing a term of type {leanRef}`p ∧ q ∧ p`, in a context with constants
-- {leanRef}`p q : Prop`, {leanRef}`hp : p` and {leanRef}`hq : q`:

从概念上讲，陈述一个定理或引入一个 {kw}`have` 声明会产生一个目标，
即构造一个具有预期类型的项的目标。例如，下面创建的目标是构建一个类型为 {leanRef}`p ∧ q ∧ p` 的项，
上下文中有常量 {leanRef}`p q : Prop`，{leanRef}`hp : p` 和 {leanRef}`hq : q`：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  --                                   PROOF_STATE: X      ^
  sorry
```
:::

-- You can write this goal as follows:

写成目标如下：

```proofState X
p : Prop
q : Prop
hp : p
hq : q
⊢ p ∧ q ∧ p
```


-- Indeed, if you replace the “sorry” by an underscore in the example
-- above, Lean will report that it is exactly this goal that has been
-- left unsolved.

事实上，如果你把上面的例子中的“sorry”换成下划线，Lean 会报告说，正是这个目标没有得到解决。

-- Ordinarily, you meet such a goal by writing an explicit term. But
-- wherever a term is expected, Lean allows us to insert instead a
-- {lit}`by <tactics>` block, where {lit}`<tactics>` is a sequence of commands,
-- separated by semicolons or line breaks. You can prove the theorem above
-- in that way:

通常情况下，你会通过写一个明确的项来满足这样的目标。但在任何需要项的地方，
Lean 允许我们插入一个 {lit}`by <tactics>` 块，其中 {lit}`<tactics>` 是一串命令，
用分号或换行符分开。你可以用下面这种方式来证明上面的定理：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

-- We often put the {leanRef}`by` keyword on the preceding line, and write the
-- example above as:

我们经常将 {leanRef}`by` 关键字放在前一行，并将上面的例子写为：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
-- ^ PROOF_STATE: intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

-- The {leanRef}`apply` tactic applies an expression, viewed as denoting a
-- function with zero or more arguments. It unifies the conclusion with
-- the expression in the current goal, and creates new goals for the
-- remaining arguments, provided that no later arguments depend on
-- them. In the example above, the command {leanRef}`apply And.intro` yields two
-- subgoals:

{leanRef}`apply` 策略应用于一个表达式，被视为表示一个有零或多个参数的函数。
它将结论与当前目标中的表达式统一起来，并为剩余的参数创建新的目标，
只要后面的参数不依赖于它们。在上面的例子中，命令 {leanRef}`apply And.intro` 产生了两个子目标：

```proofState intro
case left
p : Prop
q : Prop
hp : p
hq : q
⊢ p

case right
p : Prop
q : Prop
hp : p
hq : q
⊢ q ∧ p
```

-- The first goal is met with the command {leanRef}`exact hp`. The {leanRef}`exact`
-- command is just a variant of {leanRef}`apply` which signals that the
-- expression given should fill the goal exactly. It is good form to use
-- it in a tactic proof, since its failure signals that something has
-- gone wrong. It is also more robust than {leanRef}`apply`, since the
-- elaborator takes the expected type, given by the target of the goal,
-- into account when processing the expression that is being applied. In
-- this case, however, {leanRef}`apply` would work just as well.

第一个目标是通过命令 {leanRef}`exact hp` 来实现的。{leanRef}`exact` 命令只是 {leanRef}`apply` 的一个变体，
它表示所给的表达式应该准确地填充目标。在策略证明中使用它很有益，因为它如果失败那么表明出了问题。
它也比 {leanRef}`apply` 更稳健，因为繁饰器在处理被应用的表达式时，会考虑到目标所预期的类型。
然而，在这种情况下，{leanRef}`apply` 也可以很好地工作。

-- You can see the resulting proof term with the {kw}`#print` command:

你可以用 {kw}`#print` 命令查看所产生的证明项：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
------
#print test
```

::: TODO
Check these. Vim?
:::
-- You can write a tactic script incrementally. In VS Code, you can open
-- a window to display messages by pressing {kbd}[`Ctrl` `Shift` `Enter`], and
-- that window will then show you the current goal whenever the cursor is
-- in a tactic block. If the proof is incomplete, the token {kw}`by` is
-- decorated with a red squiggly line, and the error message contains the
-- remaining goals.

你可以循序渐进地写一个策略脚本。在 VS Code 中，你可以通过按 {kbd}[`Ctrl` `Shift` `Enter`] 打开一个窗口来显示信息，
然后只要光标在策略块中，该窗口就会显示当前的目标。如果证明是不完整的，
标记 {kw}`by` 会被装饰成一条红色的波浪线，错误信息中包含剩余的目标。

-- Tactic commands can take compound expressions, not just single
-- identifiers. The following is a shorter version of the preceding
-- proof:

策略命令可以接受复合表达式，而不仅仅是单一标识符。下面是前面证明的一个简短版本：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

-- Unsurprisingly, it produces exactly the same proof term:

不出所料，它产生了完全相同的证明项：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
 apply And.intro hp
 exact And.intro hq hp
------
#print test
```

-- Multiple tactic applications can be written in a single line by concatenating with a semicolon.

应用多个策略可以通过用分号连接写在一行中。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

-- Tactics that may produce multiple subgoals often tag them. For
-- example, the tactic {leanRef}`apply And.intro` tagged the first subgoal as
-- {goal intro}`left`, and the second as {goal intro}`right`. In the case of the {leanRef}`apply`
-- tactic, the tags are inferred from the parameters' names used in the
-- {leanRef}`And.intro` declaration. You can structure your tactics using the
-- notation {kw}`case`{lit}` <tag> => <tactics>`. The following is a structured
-- version of our first tactic proof in this chapter.

可能产生多个子目标的策略通常对子目标进行标记。例如，策略 {leanRef}`apply And.intro` 将第一个子目标标记为
{goal intro}`left`，将第二个标记为 {goal intro}`right`。在 {leanRef}`apply` 策略的情况下，
标签是从 {leanRef}`And.intro` 声明中使用的参数名称推断出来的。你可以使用符号 {kw}`case`{lit}` <tag> => <tactics>`
来结构化你的策略。下面是本章中第一个策略证明的结构化版本。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

:::leanFirst

-- You can solve the subgoal {goal intro2}`right` before {goal intro2}`left` using the {leanRef}`case`
-- notation:

使用 {leanRef}`case` 标记，你也可以在 {goal intro2}`left` 之前先解决子目标 {goal intro2}`right`：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  -- ^ PROOF_STATE: intro2
  case right =>
    apply And.intro
    case left => exact hq
  --          ^ PROOF_STATE: leftBranch
    case right => exact hp
  case left => exact hp
```
:::

-- Note that Lean hides the other goals inside the {leanRef}`case` block. After {leanRef}`case left =>`,
-- the proof state is:

注意，Lean 将其他目标隐藏在 {leanRef}`case` 块内。在 {leanRef}`case left =>` 之后，证明状态是：

```proofState leftBranch
p : Prop
q : Prop
hp : p
hq : q
⊢ q
```

-- We say that {leanRef}`case` is “focusing” on the selected goal.  Moreover, Lean flags an error
-- if the selected goal is not fully solved at the end of the {leanRef}`case`
-- block.

我们说 {leanRef}`case` 是“专注”于选定的目标。 此外，如果所选目标在 {leanRef}`case` 块的末尾没有完全解决，
Lean 会标记一个错误。

-- For simple subgoals, it may not be worth selecting a subgoal using its
-- tag, but you may still want to structure the proof. Lean also provides
-- the “bullet” notation {lit}`. <tactics>` (or {lit}`· <tactics>`) for
-- structuring proofs:

对于简单的子目标，可能不值得使用其标签来选择一个子目标，但你可能仍然想要结构化证明。
Lean 还提供了“子弹”符号 {lit}`. <tactics>`（或 {lit}`· <tactics>`）来结构化证明：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

-- # Basic Tactics
# 基本策略
%%%
tag := "basic-tactics"
%%%


:::leanFirst
-- In addition to {leanRef}`apply` and {leanRef}`exact`, another useful tactic is
-- {leanRef}`intro`, which introduces a hypothesis. What follows is an example
-- of an identity from propositional logic that we proved in a previous
-- chapter, now proved using tactics.

除了 {leanRef}`apply` 和 {leanRef}`exact` 之外，另一个有用的策略是 {leanRef}`intro`，
它引入了一个假设。下面是我们在前一章中证明的命题逻辑中的一个等价性的例子，现在用策略来证明。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```
:::

-- The {leanRef}`intro` command can more generally be used to introduce a variable of any type:

{leanRef}`intro` 命令可以更普遍地用于引入任何类型的变量：

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

-- You can use it to introduce several variables:

你可以同时引入好几个变量：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

:::setup
```
variable {α : Sort u} {p : Prop} {e : p}
```

-- As the {leanRef}`apply` tactic is a command for constructing function
-- applications interactively, the {leanRef}`intro` tactic is a command for
-- constructing function abstractions interactively (i.e., terms of the
-- form {lean (type := "∀ (x : α), p")}`fun x => e`).  As with lambda abstraction notation, the
-- {leanRef}`intro` tactic allows us to use an implicit {kw}`match`.

由于 {leanRef}`apply` 策略是一个用于交互式构造函数应用的命令，{leanRef}`intro` 策略是一个用于交互式构造函数抽象的命令
（即 {lean (type := "∀ (x : α), p")}`fun x => e` 形式的项）。 与 lambda 抽象符号一样，
{leanRef}`intro` 策略允许我们使用隐式的 {kw}`match`。
:::

```lean
example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

-- You can also provide multiple alternatives like in the {kw}`match` expression.

就像 {kw}`match` 表达式一样，你也可以提供多个选项。

```lean
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

::::leanFirst
-- The {leanRef}`intros` tactic can be used without any arguments, in which
-- case, it chooses names and introduces as many variables as it can. You
-- will see an example of this in a moment.

{leanRef}`intros` 策略可以在没有任何参数的情况下使用，在这种情况下，它选择名字并尽可能多地引入变量。
稍后你会看到一个例子。

:::leanFirst
-- The {leanRef}`assumption` tactic looks through the assumptions in context of
-- the current goal, and if there is one matching the conclusion, it
-- applies it.

{leanRef}`assumption` 策略在当前目标的背景下查看假设，如果有一个与结论相匹配的假设，它就会应用这个假设。

```lean
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```
:::

-- It will unify metavariables in the conclusion if necessary:

若有必要，它会在结论中统一元变量：

```lean
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

-- The following example uses the {leanRef}`intros` command to introduce the three variables and two hypotheses automatically:

下面的例子使用 {leanRef}`intros` 命令来自动引入三个变量和两个假设：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```
::::

:::leanFirst
-- Note that names automatically generated by Lean are inaccessible by default. The motivation is to
-- ensure your tactic proofs do not rely on automatically generated names, and are consequently more robust.
-- However, you can use the combinator {leanRef}`unhygienic` to disable this restriction.

请注意，由 Lean 自动生成的名称在默认情况下是不可访问的。其动机是为了确保你的策略证明不依赖于自动生成的名字，
并因此而更加稳健。然而，你可以使用组合器 {leanRef}`unhygienic` 来禁用这一限制。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```
:::

:::leanFirst
-- You can also use the {leanRef}`rename_i` tactic to rename the most recent inaccessible names in your context.
-- In the following example, the tactic {leanRef}`rename_i h1 _ h2` renames two of the last three hypotheses in
-- your context.

你也可以使用 {leanRef}`rename_i` 策略来重命名你的上下文中最近的不能访问的名字。在下面的例子中，
策略 {leanRef}`rename_i h1 _ h2` 在你的上下文中重命名了三个假设中的两个。

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```
:::

:::leanFirst
-- The {leanRef}`rfl` tactic solves goals that are reflexive relations applied to definitionally equal arguments.
-- Equality is reflexive:

{leanRef}`rfl` 策略解决那些应用于定义上相等的参数的自反关系的目标。
相等是自反的：

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl
```
:::

:::leanFirst
-- The {leanRef}`repeat` combinator can be used to apply a tactic several times:

{leanRef}`repeat` 组合器可以多次使用一个策略：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```
:::

:::leanFirst
-- Another tactic that is sometimes useful is the {leanRef}`revert` tactic,
-- which is, in a sense, an inverse to {leanRef}`intro`:

另一个有时很有用的策略是 {leanRef}`revert` 策略，从某种意义上说，它是对 {leanRef}`intro` 的逆：

```lean
example (x : Nat) : x = x := by
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterRevertIntro
  rfl
```

-- After {leanRef}`revert x`, the proof state is:

在 {leanRef}`revert x` 之后，证明状态是：

```proofState afterRevert
⊢ ∀ (x : Nat), x = x
```

-- After {leanRef}`intro y`, it is:

在 {leanRef}`intro y` 之后，它是：

```proofState afterRevertIntro
y : Nat
⊢ y = y
```

:::

-- Moving a hypothesis into the goal yields an implication:

将一个假设还原到目标中会产生一个蕴含：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- ^ PROOF_STATE: afterRevertH
  intro h₁
  -- ^ PROOF_STATE: afterRevertHIntro
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

-- After {leanRef}`revert h`, the proof state is:

在 {leanRef}`revert h` 之后，证明状态是：

```proofState afterRevertH
x : Nat
y : Nat
⊢ x = y → y = x
```

-- After {leanRef}`intro h₁`, it is:

在 {leanRef}`intro h₁` 之后，它是：

```proofState afterRevertHIntro
x : Nat
y : Nat
h₁ : x = y
⊢ y = x
```

:::leanFirst
-- But {leanRef}`revert` is even more clever, in that it will revert not only an
-- element of the context but also all the subsequent elements of the
-- context that depend on it. For example, reverting {leanRef (in := "revert x")}`x` in the example
-- above brings {leanRef}`h` along with it:

但是 {leanRef}`revert` 更聪明，因为它不仅会还原上下文中的一个元素，还会还原上下文中所有依赖它的后续元素。
例如，在上面的例子中，还原 {leanRef (in := "revert x")}`x` 会带来 {leanRef}`h`。

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- ^ PROOF_STATE: afterRevertXH
  intros
  apply Eq.symm
  assumption
```

-- After {leanRef}`revert x`, the goal is:

在 {leanRef}`revert x` 之后，目标是：

```proofState afterRevertXH
y : Nat
⊢ ∀ (x : Nat), x = y → y = x
```

:::

-- You can also revert multiple elements of the context at once:

你还可以一次性还原多个元素：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- ^ PROOF_STATE: revertXY
  intros
  apply Eq.symm
  assumption
```

-- After {leanRef}`revert x y`, the goal is:

在 {leanRef}`revert x y` 之后，目标是：

```proofState revertXY
⊢ ∀ (x y : Nat), x = y → y = x
```

:::leanFirst
-- You can only {leanRef}`revert` an element of the local context, that is, a
-- local variable or hypothesis. But you can replace an arbitrary
-- expression in the goal by a fresh variable using the {leanRef}`generalize`
-- tactic:

你只能 {leanRef}`revert` 局部环境中的一个元素，也就是一个局部变量或假设。
但是你可以使用 {leanRef}`generalize` 策略将目标中的任意表达式替换为新的变量：

```lean (showProofStates := "afterGen afterRevert afterIntro")
example : 3 = 3 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterIntro
  rfl
```

-- In particular, after {leanRef}`generalize`, the goal is

特别地，在 {leanRef}`generalize` 之后，目标是

```proofState afterGen
x : Nat
⊢ x = x
```

:::

-- The mnemonic in the notation above is that you are generalizing the
-- goal by setting {leanRef}`3` to an arbitrary variable {leanRef (in := "revert x")}`x`. Be careful: not
-- every generalization preserves the validity of the goal. Here,
-- {leanRef}`generalize` replaces a goal that could be proved using
-- {tactic}`rfl` with one that is not provable:

上述符号的记忆法是，你通过将 {leanRef}`3` 设定为任意变量 {leanRef (in := "revert x")}`x` 来泛化目标。
要注意：不是每一个泛化都能保留目标的有效性。这里，{leanRef}`generalize` 用一个无法证明的目标取代了一个可以用
{tactic}`rfl` 证明的目标：

```lean (showProofStates := "afterGen")
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  sorry
```

-- In this example, the {leanRef}`sorry` tactic is the analogue of the {lean}`sorry`
-- proof term. It closes the current goal, producing the usual warning
-- that {lean}`sorry` has been used. To preserve the validity of the previous
-- goal, the {leanRef}`generalize` tactic allows us to record the fact that
-- {leanRef}`3` has been replaced by {leanRef}`x`. All you need to do is to provide a
-- label, and {leanRef}`generalize` uses it to store the assignment in the local
-- context:

在这个例子中，{leanRef}`sorry` 策略是 {lean}`sorry` 证明项的类似物。它关闭了当前的目标，
产生了通常的警告：使用了 {lean}`sorry`。为了保持之前目标的有效性，{leanRef}`generalize` 策略允许我们记录
{leanRef}`3` 已经被 {leanRef}`x` 所取代的事实。你所需要做的就是提供一个标签，
{leanRef}`generalize` 使用它来存储局部上下文中的赋值：

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- ^ PROOF_STATE: afterGen
  rw [← h]
```

-- Following {leanRef}`generalize h : 3 = x`, {leanRef}`h` is a proof that {leanRef}`3 = x`:

在 {leanRef}`generalize h : 3 = x` 之后，{leanRef}`h` 是 {leanRef}`3 = x` 的证明：

```proofState afterGen
x : Nat
h : 3 = x
⊢ 2 + x = 5
```

-- Here the rewriting tactic {leanRef}`rw` uses {leanRef}`h` to replace
-- {leanRef}`x` by {leanRef}`3` again. The {leanRef}`rw` tactic will be discussed below.

这里重写策略 {leanRef}`rw` 使用 {leanRef}`h` 再次将 {leanRef}`x` 替换为 {leanRef}`3`。
{leanRef}`rw` 策略下文将继续讨论。

-- # More Tactics
# 更多策略
%%%
tag := "more-tactics"
%%%


:::leanFirst
-- Some additional tactics are useful for constructing and destructing
-- propositions and data. For example, when applied to a goal of the form
-- {leanRef}`p ∨ q`, you use tactics such as {leanRef}`apply Or.inl` and
-- {leanRef}`apply Or.inr`.  Conversely, the {leanRef}`cases` tactic can be used to decompose a
-- disjunction:

一些额外的策略对于建构和析构命题以及数据很有用。例如，当应用于形式为 {leanRef}`p ∨ q` 的目标时，
你可以使用 {leanRef}`apply Or.inl` 和 {leanRef}`apply Or.inr` 等策略。
反之，{leanRef}`cases` 策略可以用来分解一个析取：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```
:::

-- Note that the syntax is similar to the one used in {kw}`match` expressions.
-- The new subgoals can be solved in any order:

注意，该语法与 {kw}`match` 表达式中使用的语法相似。新的子目标可以按任何顺序解决：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

-- You can also use a (unstructured) {leanRef}`cases` without the {leanRef}`with` and a tactic
-- for each alternative:

你也可以使用一个（非结构化的）{leanRef}`cases`，而不使用 {leanRef}`with`，并为每个备选情况制定一个策略：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

-- The (unstructured) {leanRef}`cases` is particularly useful when you can close several
-- subgoals using the same tactic:

（非结构化的）{leanRef}`cases` 在你可以用同一个策略来解决子任务时格外有用：

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

-- You can also use the combinator {lit}`tac1 `{tactic}`<;>`{lit}` tac2` to apply {lit}`tac2` to each
-- subgoal produced by tactic {lit}`tac1`:

你也可以使用组合器 {lit}`tac1 `{tactic}`<;>`{lit}` tac2`，将 {lit}`tac2` 应用于策略 {lit}`tac1` 产生的每个子目标：

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

:::leanFirst
-- You can combine the unstructured {leanRef}`cases` tactic with the {leanRef}`case` and {leanRef}`.` notation:

你可以与 {leanRef}`.` 符号相结合使用非结构化的 {leanRef}`cases` 策略：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```
:::


-- The {leanRef}`cases` tactic can also be used to
-- decompose a conjunction:

{leanRef}`cases` 策略也被用来分解一个合取：

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
  --             ^ PROOF_STATE: afterIntroCase
```


-- In this example, there is only one goal after the {leanRef}`cases` tactic is
-- applied, with {leanRef}`h`{lit}`  :  `{leanRef}`p ∧ q` replaced by a pair of assumptions,
-- {leanRef}`hp`{lit}`  :  `{leanRef}`p` and {leanRef}`hq`{lit}`  :  `{leanRef}`q`:

在这个例子中，应用 {leanRef}`cases` 策略后只有一个目标，{leanRef}`h`{lit}`  :  `{leanRef}`p ∧ q` 被一对假设取代，
{leanRef}`hp`{lit}`  :  `{leanRef}`p` 和 {leanRef}`hq`{lit}`  :  `{leanRef}`q`：

```proofState afterIntroCase
case intro
p : Prop
q : Prop
hp : p
hq : q
⊢ q ∧ p
```

-- The {leanRef}`constructor` tactic applies the unique
-- constructor for conjunction, {lean}`And.intro`.

{leanRef}`constructor` 策略应用了唯一一个合取构造子 {lean}`And.intro`。

-- With these tactics, an
-- example from the previous section can be rewritten as follows:

有了这些策略，上一节的一个例子可以改写如下：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr; exact hr
```

-- You will see in {ref "inductive-types"}[Inductive Types] that
-- these tactics are quite general. The {leanRef}`cases` tactic can be used to
-- decompose any element of an inductively defined type; {leanRef}`constructor`
-- always applies the first applicable constructor of an inductively defined type.
-- For example, you can use {leanRef}`cases` and {leanRef}`constructor` with an existential quantifier:

你将在 {ref "inductive-types"}[归纳类型] 一章中看到，这些策略是相当通用的。
{leanRef}`cases` 策略可以用来分解递归定义类型的任何元素；{leanRef}`constructor`
总是应用递归定义类型的第一个适用构造子。例如，你可以使用 {leanRef}`cases` 和 {leanRef}`constructor` 与一个存在量词：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

-- Here, the {leanRef}`constructor` tactic leaves the first component of the
-- existential assertion, the value of {leanRef}`x`, implicit. It is represented
-- by a metavariable, which should be instantiated later on. In the
-- previous example, the proper value of the metavariable is determined
-- by the tactic {leanRef}`exact px`, since {leanRef}`px` has type {leanRef}`p x`. If you want
-- to specify a witness to the existential quantifier explicitly, you can
-- use the {tactic}`exists` tactic instead:

在这里，{leanRef}`constructor` 策略将存在性断言的第一个组成部分，即 {leanRef}`x` 的值，保留为隐式的。
它是由一个元变量表示的，这个元变量以后应该被实例化。在前面的例子中，元变量的正确值是由策略 {leanRef}`exact px` 决定的，
因为 {leanRef}`px` 的类型是 {leanRef}`p x`。如果你想明确指定存在量词的存在者，你可以使用 {tactic}`exists` 策略来代替：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

-- Here is another example:

另一个例子：

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
```

-- These tactics can be used on data just as well as propositions. In the
-- next example, they are used to define functions which swap the
-- components of the product and sum types:

这些策略既可以用在命题上，也可以用在数据上。在下面的两个例子中，它们被用来定义交换乘法和加法类型组件的函数：

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

-- Note that up to the names we have chosen for the variables, the
-- definitions are identical to the proofs of the analogous propositions
-- for conjunction and disjunction. The {leanRef}`cases` tactic will also do a
-- case distinction on a natural number:

在我们为变量选择的名称之前，它们的定义与有关合取和析取的类似命题的证明是相同的。
{leanRef}`cases` 策略也会对自然数进行逐情况区分：

```lean
open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

-- The {leanRef}`cases` tactic, and its companion, the {tactic}`induction` tactic, are discussed in greater detail in
-- the {ref "tactics-for-inductive-types"}[Tactics for Inductive Types] section.

{leanRef}`cases` 策略及其同伴 {tactic}`induction` 策略将在 {ref "tactics-for-inductive-types"}[归纳类型的策略] 一节中详述。

:::leanFirst
-- The {leanRef}`contradiction` tactic searches for a contradiction among the hypotheses of the current goal:

{leanRef}`contradiction` 策略搜索当前目标的假设中的矛盾：

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```
:::

:::leanFirst
-- You can also use {tactic}`match` in tactic blocks.

你也可以在策略块中使用 {tactic}`match`：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr
```
:::

:::leanFirst
-- You can “combine” {leanRef}`intro` with {tactic}`match` and write the previous examples as follows:

你可以将 {leanRef}`intro` 与 {tactic}`match` 结合起来，然后上例就可以如下地写出：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption
```
:::

-- # Structuring Tactic Proofs
# 结构化策略证明
%%%
tag := "structuring-tactic-proofs"
%%%

-- Tactics often provide an efficient way of building a proof, but long
-- sequences of instructions can obscure the structure of the
-- argument. In this section, we describe some means that help provide
-- structure to a tactic-style proof, making such proofs more readable
-- and robust.

策略通常提供了建立证明的有效方法，但一长串指令会掩盖论证的结构。在这一节中，我们将描述一些有助于为策略式证明提供结构的方法，使这种证明更易读，更稳健。

:::leanFirst
-- One thing that is nice about Lean's proof-writing syntax is that it is
-- possible to mix term-style and tactic-style proofs, and pass between
-- the two freely. For example, the tactics {leanRef}`apply` and {leanRef}`exact`
-- expect arbitrary terms, which you can write using {kw}`have`, {kw}`show`,
-- and so on. Conversely, when writing an arbitrary Lean term, you can
-- always invoke the tactic mode by inserting a {kw}`by`
-- block. The following is a somewhat toy example:

Lean 的证明写作语法的一个优点是，它可以混合项式和策略式证明，并在两者之间自由转换。
例如，策略 {leanRef}`apply` 和 {leanRef}`exact` 可以传入任意的项，你可以用 {kw}`have`，{kw}`show` 等等来写这些项。
反之，当写一个任意的 Lean 项时，你总是可以通过插入一个 {kw}`by` 块来调用策略模式。下面是一个简易例子：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```
:::

-- The following is a more natural example:

更自然一点：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

:::leanFirst
-- In fact, there is a {tactic}`show` tactic, which is similar to the
-- {kw}`show` expression in a proof term. It simply declares the type of the
-- goal that is about to be solved, while remaining in tactic
-- mode.

事实上，有一个 {tactic}`show` 策略，它类似于证明项中的 {kw}`show` 表达式。
它只是简单地声明即将被解决的目标的类型，同时保持策略模式。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```
:::

-- The {tactic}`show` tactic can actually be used to rewrite a goal to something definitionally equivalent:

{tactic}`show` 策略其实可以被用来重写一些定义等价的目标：

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

-- There is also a {tactic}`have` tactic, which introduces a new subgoal, just as when writing proof terms:

还有一个 {tactic}`have` 策略，它引入了一个新的子目标，就像写证明项时一样：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

:::leanFirst
-- As with proof terms, you can omit the label in the {tactic}`have` tactic, in
-- which case, the default label {leanRef}`this` is used:

与证明项一样，你可以省略 {tactic}`have` 策略中的标签，在这种情况下，将使用默认标签 {leanRef}`this`：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```
:::

:::leanFirst
-- The types in a {tactic}`have` tactic can be omitted, so you can write
-- {lit}`have hp := h.left` and {lit}`have hqr := h.right`.  In fact, with this
-- notation, you can even omit both the type and the label, in which case
-- the new fact is introduced with the label {leanRef}`this`:

{tactic}`have` 策略中的类型可以省略，所以你可以写 {lit}`have hp := h.left` 和 {lit}`have hqr := h.right`。
事实上，使用这种符号，你甚至可以省略类型和标签，在这种情况下，新的事实是用标签 {leanRef}`this` 引入的：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```
:::

-- Lean also has a {tactic}`let` tactic, which is similar to the {tactic}`have`
-- tactic, but is used to introduce local definitions instead of
-- auxiliary facts. It is the tactic analogue of a {kw}`let` in a proof
-- term:

Lean 还有一个 {tactic}`let` 策略，它类似于 {tactic}`have` 策略，但用于引入局部定义而不是辅助事实。
它是证明项中 {kw}`let` 的策略模拟：

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

-- As with {tactic}`have`, you can leave the type implicit by writing
-- {lit}`let a := 3 * 2`. The difference between {tactic}`let` and {tactic}`have` is that
-- {tactic}`let` introduces a local definition in the context, so that the
-- definition of the local declaration can be unfolded in the proof.

与 {tactic}`have` 一样，你可以通过写 {lit}`let a := 3 * 2` 来让类型隐式。
{tactic}`let` 和 {tactic}`have` 的区别在于 {tactic}`let` 在上下文中引入了一个局部定义，
这样局部声明的定义就可以在证明中展开。

-- We have used {leanRef}`.` to create nested tactic blocks.  In a nested block,
-- Lean focuses on the first goal, and generates an error if it has not
-- been fully solved at the end of the block. This can be helpful in
-- indicating the separate proofs of multiple subgoals introduced by a
-- tactic. The notation {leanRef}`.` is whitespace sensitive and relies on the indentation
-- to detect whether the tactic block ends. Alternatively, you can
-- define tactic blocks using curly braces and semicolons:

我们已经使用 {leanRef}`.` 来创建嵌套的策略块。在嵌套块中，Lean 聚焦于第一个目标，
如果该目标在块结束时还没有被完全解决，就会产生一个错误。这有助于指示由一个策略引入的多个子目标的独立证明。
符号 {leanRef}`.` 是空格敏感的，并依靠缩进来检测策略块是否结束。或者，你可以使用大括号和分号来定义策略块：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

-- It is useful to use indentation to structure proof: every time a tactic
-- leaves more than one subgoal, we separate the remaining subgoals by
-- enclosing them in blocks and indenting.  Thus if the application of
-- theorem {lit}`foo` to a single goal produces four subgoals, one would
-- expect the proof to look like this:

使用缩进来构造证明是很有用的：每当一个策略留下一个以上的子目标时，我们就通过将剩余的子目标封闭在块中并缩进来分离它们。
因此，如果将定理 {lit}`foo` 应用于一个单一的目标产生了四个子目标，人们会期望证明看起来像这样：

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

-- or

或者

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

-- or

或者

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

-- # Tactic Combinators
# 策略组合子
%%%
tag := "tactic-combinators"
%%%

-- _Tactic combinators_ are operations that form new tactics from old
-- ones. A sequencing combinator is already implicit in the {kw}`by` block:

_策略组合子（Tactic combinator）_ 是从旧策略形成新策略的操作。在 {kw}`by` 块中已经隐含了一个顺序组合子：

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

-- Here, {leanRef}`apply Or.inl; assumption` is functionally equivalent to a
-- single tactic which first applies {leanRef}`apply Or.inl` and then applies
-- {leanRef}`assumption`.

在这里，{leanRef}`apply Or.inl; assumption` 在功能上等同于一个单一的策略，
它首先应用 {leanRef}`apply Or.inl`，然后应用 {leanRef}`assumption`。

-- In {lit}`t₁ `{tactic}`<;>`{lit}` t₂`, the {leanRef}`<;>` operator provides a _parallel_ version of the sequencing operation:
-- {lit}`t₁` is applied to the current goal, and then {lit}`t₂` is applied to _all_ the resulting subgoals:

在 {lit}`t₁ `{tactic}`<;>`{lit}` t₂` 中，{leanRef}`<;>` 操作符提供了顺序操作的一个 _并行_ 版本：
{lit}`t₁` 被应用于当前的目标，然后 {lit}`t₂` 被应用于 _所有_ 产生的子目标：

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

-- This is especially useful when the resulting goals can be finished off
-- in a uniform way, or, at least, when it is possible to make progress
-- on all of them uniformly.

当产生的目标可以以统一的方式完成时，或者至少当可以在所有目标上统一取得进展时，这特别有用。

-- The {tactic}`first`{lit}` | t₁ | t₂ | ... | tₙ` applies each {lit}`tᵢ` until one succeeds, or else fails:

{tactic}`first`{lit}` | t₁ | t₂ | ... | tₙ` 应用每个 {lit}`tᵢ` 直到其中一个成功，否则失败：

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

-- In the first example, the left branch succeeds, whereas in the second one, it is the right one that succeeds.
-- In the next three examples, the same compound tactic succeeds in each case:

在第一个例子中，左边的分支成功了，而在第二个例子中，右边的分支成功了。在接下来的三个例子中，同样的复合策略在每种情况下都成功了：

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

-- The tactic tries to solve the left disjunct immediately by assumption;
-- if that fails, it tries to focus on the right disjunct; and if that
-- doesn't work, it invokes the assumption tactic.

该策略尝试立即通过 assumption 解决左边的析取项；如果失败了，它尝试聚焦于右边的析取项；如果这也不起作用，它就调用 assumption 策略。

:::leanFirst
-- You will have no doubt noticed by now that tactics can fail. Indeed,
-- it is the “failure” state that causes the _first_ combinator to
-- backtrack and try the next tactic. The {leanRef}`try` combinator builds a
-- tactic that always succeeds, though possibly in a trivial way:
-- {tactic}`try`{lit}` t` executes {lit}`t` and reports success, even if {lit}`t` fails. It is
-- equivalent to {tactic}`first`{lit}` | t | `{tactic}`skip`, where {tactic}`skip` is a tactic that does
-- nothing (and succeeds in doing so). In the next example, the second
-- {leanRef}`constructor` succeeds on the right conjunct {leanRef}`q ∧ r` (remember that
-- disjunction and conjunction associate to the right) but fails on the
-- first. The {leanRef}`try` tactic ensures that the sequential composition
-- succeeds:

毫无疑问，你现在已经注意到策略会失败。事实上，正是“失败”状态导致了 {leanRef}`first` 组合子回溯并尝试下一个策略。
{leanRef}`try` 组合子建立了一个总是成功的策略，尽管可能是以一种平凡的方式：
{tactic}`try`{lit}` t` 执行 {lit}`t` 并报告成功，即使 {lit}`t` 失败。
它等同于 {tactic}`first`{lit}` | t | `{tactic}`skip`，其中 {tactic}`skip` 是一个什么都不做的策略（并且成功地做到了）。
在下一个例子中，第二个 {leanRef}`constructor` 在右边的合取项 {leanRef}`q ∧ r` 上成功了（记住析取和合取是向右结合的），
但在第一个合取项上失败了。{leanRef}`try` 策略确保了顺序组合的成功：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```
:::

-- Be careful: {tactic}`repeat`{lit}` (`{tactic}`try`{lit}` t)` will loop forever, because the inner tactic never fails.

小心：{tactic}`repeat`{lit}` (`{tactic}`try`{lit}` t)` 将永远循环下去，因为内部策略永远不会失败。

-- In a proof, there are often multiple goals outstanding. Parallel
-- sequencing is one way to arrange it so that a single tactic is applied
-- to multiple goals, but there are other ways to do this. For example,
-- {tactic}`all_goals`{lit}` t` applies {lit}`t` to all open goals:

在证明中，经常会有多个未完成的目标。并行顺序是安排将单一策略应用于多个目标的一种方式，但还有其他方式可以做到这一点。
例如，{tactic}`all_goals`{lit}` t` 将 {lit}`t` 应用于所有开启的目标：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

-- In this case, the {tactic}`any_goals` tactic provides a more robust solution.
-- It is similar to {tactic}`all_goals`, except it succeeds if its argument
-- succeeds on at least one goal:

在这种情况下，{tactic}`any_goals` 策略提供了一个更稳健的解决方案。
它类似于 {tactic}`all_goals`，只是如果它的参数在至少一个目标上成功，它就成功：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

-- The first tactic in the {kw}`by` block below repeatedly splits
-- conjunctions:

下面 {kw}`by` 块中的第一个策略重复地拆分合取项：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

-- In fact, we can compress the full tactic down to one line:

事实上，我们可以把完整的策略压缩到一行：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

-- The combinator {tactic}`focus`{lit}` t` ensures that {lit}`t` only effects the current
-- goal, temporarily hiding the others from the scope. So, if {lit}`t`
-- ordinarily only effects the current goal, {tactic}`focus`{lit}` (`{tactic}`all_goals`{lit}` t)` has
-- the same effect as {lit}`t`.

组合子 {tactic}`focus`{lit}` t` 确保 {lit}`t` 只影响当前的目标，暂时将其他目标从作用域中隐藏。
所以，如果 {lit}`t` 通常只影响当前的目标，{tactic}`focus`{lit}` (`{tactic}`all_goals`{lit}` t)` 与 {lit}`t` 有同样的效果。

-- # Rewriting
# 重写
%%%
tag := "rewriting"
%%%

-- The {tactic}`rw` tactic and the {tactic}`simp` tactic
-- were introduced briefly in {ref "calculational-proofs"}[Calculational Proofs]. In this
-- section and the next, we discuss them in greater detail.

{tactic}`rw` 策略和 {tactic}`simp` 策略在 {ref "calculational-proofs"}[计算式证明] 中被简要介绍过。
在这一节和下一节中，我们将更详细地讨论它们。

:::setup
```
variable (x y : α) (h : x = y)
theorem add_comm : ∀ (x y : Nat), x + y = y + x := by omega
```

-- The {tactic}`rw` tactic provides a basic mechanism for applying
-- substitutions to goals and hypotheses, providing a convenient and
-- efficient way of working with equality. The most basic form of the
-- tactic is {tactic}`rw`{lit}` [t]`, where {lit}`t` is a term whose type asserts an
-- equality. For example, {lit}`t` can be a hypothesis {lean}`h : x = y` in the
-- context; it can be a general lemma, like
-- {lean}`add_comm : ∀ x y, x + y = y + x`, in which the rewrite tactic tries to find suitable
-- instantiations of {lean}`x` and {lean}`y`; or it can be any compound term
-- asserting a concrete or general equation. In the following example, we
-- use this basic form to rewrite the goal using a hypothesis.

{tactic}`rw` 策略提供了一个对目标和假设应用替换的基本机制，提供了一个方便和有效的方法来处理等式。
该策略最基本的形式是 {tactic}`rw`{lit}` [t]`，其中 {lit}`t` 是一个其类型断言为等式的项。
例如，{lit}`t` 可以是上下文中的一个假设 {lean}`h : x = y`；
它可以是一个一般的引理，比如 {lean}`add_comm : ∀ x y, x + y = y + x`，
其中重写策略试图找到 {lean}`x` 和 {lean}`y` 的合适实例；
或者它可以是任何断言具体或一般方程的复合项。在下面的例子中，我们使用这种基本形式，利用一个假设来重写目标。

:::

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

:::setup
```
variable (t : α)
```

-- In the example above, the first use of {leanRef}`rw` replaces {leanRef}`k` with
-- {leanRef}`0` in the goal {leanRef}`f k = 0`. Then, the second one replaces {leanRef}`f 0`
-- with {leanRef}`0`. The tactic automatically closes any goal of the form
-- {lean}`t = t`. Here is an example of rewriting using a compound expression:

在上面的例子中，第一次使用 {leanRef}`rw` 将目标 {leanRef}`f k = 0` 中的 {leanRef}`k` 替换为 {leanRef}`0`。
然后，第二次将 {leanRef}`f 0` 替换为 {leanRef}`0`。该策略会自动关闭任何形式为 {lean}`t = t` 的目标。
下面是一个使用复合表达式重写的例子：

:::

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

-- Here, {leanRef}`h hq` establishes the equation {leanRef}`x = y`.

在这里，{leanRef}`h hq` 建立了等式 {leanRef}`x = y`。

-- Multiple rewrites can be combined using the notation {tactic}`rw`{lit}` [t_1, ..., t_n]`,
-- which is just shorthand for {tactic}`rw`{lit}` [t_1]; ...; `{tactic}`rw`{lit}` [t_n]`. The previous example can be written as follows:

多个重写可以用 {tactic}`rw`{lit}` [t_1, ..., t_n]` 符号组合起来，
这只是 {tactic}`rw`{lit}` [t_1]; ...; `{tactic}`rw`{lit}` [t_n]` 的简写。前面的例子可以写成如下形式：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

-- By default, {leanRef}`rw` uses an equation in the forward direction, matching
-- the left-hand side with an expression, and replacing it with the
-- right-hand side. The notation {lit}`←t` can be used to instruct the
-- tactic to use the equality {lit}`t` in the reverse direction.

默认情况下，{leanRef}`rw` 使用正向的等式，将左手边与一个表达式匹配，并将其替换为右手边。
{lit}`←t` 符号可以用来指示策略在反方向使用等式 {lit}`t`。

```lean
variable (a b : Nat) (f : Nat → Nat)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

-- In this example, the term {leanRef}`←h₁` instructs the rewriter to replace
-- {leanRef}`b` with {leanRef}`a`. In the editors, you can type the backwards arrow as
-- {kbd}`\l`. You can also use the ASCII equivalent, {lit}`<-`.

在这个例子中，项 {leanRef}`←h₁` 指示重写器将 {leanRef}`b` 替换为 {leanRef}`a`。
在编辑器中，你可以把向后的箭头输入为 {kbd}`\l`。你也可以使用 ASCII 等效符号 {lit}`<-`。

-- Sometimes the left-hand side of an identity can match more than one
-- subterm in the pattern, in which case the {tactic}`rw` tactic chooses the
-- first match it finds when traversing the term. If that is not the one
-- you want, you can use additional arguments to specify the appropriate
-- subterm.

有时，恒等式的左手边可以匹配模式中的多个子项，在这种情况下，{tactic}`rw` 策略会选择它在遍历该项时发现的第一个匹配。
如果那不是你想要的，你可以使用额外的参数来指定合适的子项。

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

:::TODO
-- Get the intermediate proof states from `rw` into the reference ring to help these examples be better
将 `rw` 的中间证明状态放入参考环中，以帮助这些例子变得更好
:::

-- In the first example above, the first step rewrites {leanRef}`a + b + c` to
-- {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)`. The next step applies commutativity to the term
-- {leanRef}`b + c`; without specifying the argument, the tactic would instead rewrite
-- {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)` to {lit}`(`{leanRef}`b + c`{lit}`) + `{leanRef}`a`. Finally, the last step applies
-- associativity in the reverse direction, rewriting {leanRef}`a`{lit}` + (`{leanRef}`c`{lit}`  +  `{leanRef}`b`{lit}`)` to
-- {leanRef}`a + c + b`. The next two examples instead apply associativity to
-- move the parenthesis to the right on both sides, and then switch {leanRef}`b`
-- and {leanRef}`c`. Notice that the last example specifies that the rewrite
-- should take place on the right-hand side by specifying the second
-- argument to {leanRef}`Nat.add_comm`.

在上面的第一个例子中，第一步将 {leanRef}`a + b + c` 重写为 {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)`。
下一步对 {leanRef}`b + c` 项应用交换律；如果不指定参数，该策略将把 {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)` 重写为 {lit}`(`{leanRef}`b + c`{lit}`) + `{leanRef}`a`。
最后，最后一步在反方向应用结合律，将 {leanRef}`a`{lit}` + (`{leanRef}`c`{lit}`  +  `{leanRef}`b`{lit}`)` 重写为 {leanRef}`a + c + b`。
接下来的两个例子则是应用结合律，将两边的括号移到右边，然后交换 {leanRef}`b` 和 {leanRef}`c`。
注意，最后一个例子通过指定 {leanRef}`Nat.add_comm` 的第二个参数，指定了重写应该发生在右手边。

注意，最后一个例子通过指定 {leanRef}`Nat.add_comm` 的第二个参数，指定了重写应该发生在右手边。

-- By default, the {leanRef}`rw` tactic affects only the goal. The notation
-- {tactic}`rw`{lit}`  [t]  `{kw}`at`{lit}` h` applies the rewrite

默认情况下，{leanRef}`rw` 策略只影响目标。{tactic}`rw`{lit}` [t] `{kw}`at`{lit}` h` 符号将重写应用于假设 {lit}`h`。

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

-- The first step, {leanRef}`rw [Nat.add_zero] at h`, rewrites the hypothesis {leanRef}`a + 0 = 0` to {leanRef}`a = 0`.
-- Then the new hypothesis {leanRef}`a = 0` is used to rewrite the goal to {leanRef}`f 0`{lit}`  =  `{leanRef}`f 0`.

第一步，{leanRef}`rw [Nat.add_zero] at h`，将假设 {leanRef}`a + 0 = 0` 重写为 {leanRef}`a = 0`。
然后新的假设 {leanRef}`a = 0` 被用来将目标重写为 {leanRef}`f 0`{lit}` = `{leanRef}`f 0`。

:::leanFirst
-- The {leanRef}`rw` tactic is not restricted to propositions.
-- In the following example, we use {tactic}`rw`{lit}`  [h]  `{kw}`at`{lit}` t` to rewrite the hypothesis {leanRef}`t : Tuple α n` to {leanRef}`t : Tuple α`{lit}` 0`.

{leanRef}`rw` 策略并不局限于命题。在下面的例子中，我们使用 {tactic}`rw`{lit}` [h] `{kw}`at`{lit}` t` 来将假设 {leanRef}`t : Tuple α n` 重写为 {leanRef}`t : Tuple α`{lit}` 0`。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```
:::

-- # Using the Simplifier
# 使用简化器
%%%
tag := "using-the-simplifier"
%%%

-- Whereas {tactic}`rw` is designed as a surgical tool for manipulating a
-- goal, the simplifier offers a more powerful form of automation. A
-- number of identities in Lean's library have been tagged with the
-- {attr}`[simp]` attribute, and the {tactic}`simp` tactic uses them to iteratively
-- rewrite subterms in an expression.

虽然 {tactic}`rw` 被设计成操作目标的“手术刀”，但简化器（Simplifier）提供了一种更强大的自动化形式。
Lean 库中的许多恒等式都被标记了 {attr}`[simp]` 属性，而 {tactic}`simp` 策略使用它们来迭代地重写表达式中的子项。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

-- In the first example, the left-hand side of the equality in the goal
-- is simplified using the usual identities involving 0 and 1, reducing
-- the goal to {leanRef}`x * y`{lit}`  =  `{leanRef}`x * y`. At that point, {leanRef}`simp` applies
-- reflexivity to finish it off. In the second example, {leanRef}`simp` reduces
-- the goal to {leanRef}`p (x * y)`, at which point the assumption {leanRef}`h`
-- finishes it off. Here are some more examples
-- with lists:

在第一个例子中，目标中等式的左手边使用涉及 0 和 1 的常用恒等式进行简化，将目标归约为 {leanRef}`x * y`{lit}` = `{leanRef}`x * y`。
在那一点上，{leanRef}`simp` 应用自反性来完成它. 在第二个例子中，{leanRef}`simp` 将目标归约为 {leanRef}`p (x * y)`，此时假设 {leanRef}`h` 完成了它。
下面是更多关于列表的例子：

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

-- As with {leanRef}`rw`, you can use the keyword {leanRef}`at` to simplify a hypothesis:

与 {leanRef}`rw` 一样，你可以使用关键字 {leanRef}`at` 来简化一个假设：

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

-- Moreover, you can use a “wildcard” asterisk to simplify all the hypotheses and the goal:

此外，你可以使用“通配符”星号来简化所有的假设和目标：

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

:::setup
```
variable (x y z : Nat)
```

-- For operations that are commutative and associative, like
-- multiplication on the natural numbers, the simplifier uses these two
-- facts to rewrite an expression, as well as _left commutativity_. In
-- the case of multiplication the latter is expressed as follows:
-- {lean}`x * (y * z) = y * (x * z)`. The {leanRef}`local` modifier tells the simplifier
-- to use these rules in the current file (or section or namespace, as
-- the case may be). It may seem that commutativity and
-- left-commutativity are problematic, in that repeated application of
-- either causes looping. But the simplifier detects identities that
-- permute their arguments, and uses a technique known as _ordered
-- rewriting_. This means that the system maintains an internal ordering
-- of terms, and only applies the identity if doing so decreases the
-- order. With the three identities mentioned above, this has the effect
-- that all the parentheses in an expression are associated to the right,
-- and the expressions are ordered in a canonical (though somewhat
-- arbitrary) way. Two expressions that are equivalent up to
-- associativity and commutativity are then rewritten to the same
-- canonical form.

对于可交换和可结合的操作，如自然数上的乘法，简化器使用这两个事实来重写表达式，以及 _左交换律（Left commutativity）_。
在乘法的情况下，后者表示如下：{lean}`x * (y * z) = y * (x * z)`。
{leanRef}`local` 修饰符告诉简化器在当前文件（或章节或命名空间，视情况而定）中使用这些规则。
看起来交换律和左交换律是有问题的，因为重复应用其中任何一个都会导致循环。
但简化器会检测置换其参数的恒等式，并使用一种被称为 _有序重写（Ordered rewriting）_ 的技术。
这意味着系统维持着项的内部排序，并且只有在这样做会降低排序的情况下才应用恒等式。
有了上面提到的三个恒等式，其效果是表达式中的所有括号都向右结合，并且表达式以一种规范的（虽然有些随意）方式排序。
在结合律和交换律下等价的两个表达式会被重写为相同的规范形式。
:::

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
------
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

-- As with {tactic}`rw`, you can send {tactic}`simp` a list of facts to use,
-- including general lemmas, local hypotheses, definitions to unfold, and
-- compound expressions. The {tactic}`simp` tactic also recognizes the {lit}`←t`
-- syntax that {tactic}`rewrite` does. In any case, the additional rules are
-- added to the collection of identities that are used to simplify a
-- term.

与 {tactic}`rw` 一样，你可以向 {tactic}`simp` 发送一个要使用的列表，
包括一般的引理、局部假设、要展开的定义和复合表达式。
{tactic}`simp` 策略也能识别 {tactic}`rewrite` 所能识别的 {lit}`←t` 语法。
在任何情况下，额外的规则都会被添加到用于简化项的恒等式集合中。

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

-- A common idiom is to simplify a goal using local hypotheses:

一个常见的习惯用法是使用局部假设来简化目标：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

:::leanFirst
-- To use all the hypotheses present in the local context when
-- simplifying, we can use the wildcard symbol, {leanRef}`*`:

为了在简化时使用局部上下文中存在的所有假设，我们可以使用通配符 {leanRef}`*`：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```
:::

-- Here is another example:

这里有另一个例子：

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_comm]
```

:::leanFirst
-- The simplifier will also do propositional rewriting. For example,
-- using the hypothesis {leanRef (in := "p ∧ q")}`p`, it rewrites {leanRef}`p ∧ q` to {leanRef (in := "p ∨ q")}`q` and {leanRef}`p ∨ q` to {lean}`True`,
-- which it then proves trivially. Iterating such
-- rewrites produces nontrivial propositional reasoning.

简化器也会做命题重写。例如，使用假设 {leanRef (in := "p ∧ q")}`p`，
它将 {leanRef}`p ∧ q` 重写为 {leanRef (in := "p ∨ q")}`q`，
将 {leanRef}`p ∨ q` 重写为 {lean}`True`，然后它平凡地证明了这一点。
迭代这样的重写会产生非平凡的命题推理。

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```
:::

-- The next example simplifies all the hypotheses, and then uses them to prove the goal.

下一个例子简化了所有的假设，然后用它们来证明目标。

```lean
set_option linter.unusedVariables false
------
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

-- One thing that makes the simplifier especially useful is that its
-- capabilities can grow as a library develops. For example, suppose we
-- define a list operation that symmetrizes its input by appending its
-- reversal:

使简化器特别有用的一点是，它的能力可以随着库的发展而增长。
例如，假设我们定义了一个列表操作，通过附加其反转来使其输入对称：

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

:::leanFirst
-- Then for any list {leanRef (in := "mk_symm xs")}`xs`, {leanRef}`(mk_symm xs).reverse` is equal to {leanRef}`mk_symm xs`,
-- which can easily be proved by unfolding the definition:

那么对于任何列表 {leanRef (in := "mk_symm xs")}`xs`，{leanRef}`(mk_symm xs).reverse` 等于 {leanRef}`mk_symm xs`，
这可以通过展开定义轻松证明：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```
:::

-- We can now use this theorem to prove new results:

我们现在可以用这个定理来证明新的结果：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
       : (mk_symm xs).reverse = mk_symm xs := by
 simp [mk_symm]
------
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

-- But using {leanRef}`reverse_mk_symm` is generally the right thing to do, and
-- it would be nice if users did not have to invoke it explicitly. You can
-- achieve that by marking it as a simplification rule when the theorem
-- is defined:

但是使用 {leanRef}`reverse_mk_symm` 通常是正确的做法，如果用户不必显式地调用它，那就更好了。
你可以在定义定理时将其标记为简化规则来实现：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

-- The notation {leanRef}`@[simp]` declares {leanRef}`reverse_mk_symm` to have the
-- {attr}`[simp]` attribute, and can be spelled out more explicitly:

符号 {leanRef}`@[simp]` 声明 {leanRef}`reverse_mk_symm` 具有 {attr}`[simp]` 属性，可以更明确地拼写出来：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

-- The attribute can also be applied any time after the theorem is declared:

该属性也可以在定理声明后的任何时间应用：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

:::leanFirst
-- Once the attribute is applied, however, there is no way to permanently
-- remove it; it persists in any file that imports the one where the
-- attribute is assigned. As we will discuss further in
-- {ref "attributes"}[Attributes], one can limit the scope of an attribute to the
-- current file or section using the {leanRef}`local` modifier:

然而，一旦应用了该属性，就没有办法永久地删除它；它在任何导入了分配该属性的文件中都会持续存在。
正如我们将在 {ref "attributes"}[属性] 中进一步讨论的那样，
我们可以使用 {leanRef}`local` 修饰符将属性的范围限制在当前文件或章节中：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```
:::

-- Outside the section, the simplifier will no longer use
-- {leanRef}`reverse_mk_symm` by default.
在 section 之外，化简器默认将不再使用 {leanRef}`reverse_mk_symm`。

-- Note that the various {leanRef}`simp` options we have discussed—giving an
-- explicit list of rules, and using {leanRef}`at` to specify the location—can be combined,
-- but the order they are listed is rigid. You can see the correct order
-- in an editor by placing the cursor on the {leanRef}`simp` identifier to see
-- the documentation string that is associated with it.
注意，我们讨论过的各种 {leanRef}`simp` 选项，即给出显式的规则列表，以及使用 {leanRef}`at` 指定位置，可以组合使用，但它们列出的顺序是固定的。
你可以在编辑器中通过将光标放在 {leanRef}`simp` 标识符上，查看与其关联的文档字符串，从而看到正确的顺序。

:::leanFirst
-- There are two additional modifiers that are useful. By default,
-- {leanRef}`simp` includes all theorems that have been marked with the
-- attribute {attr}`[simp]`. Writing {leanRef}`simp only` excludes these defaults,
-- allowing you to use a more explicitly crafted list of
-- rules. In the examples below, the minus sign and
-- {leanRef}`only` are used to block the application of {leanRef}`reverse_mk_symm`.
还有两个非常有用的修饰符。默认情况下，{leanRef}`simp` 包含所有标记了 {attr}`[simp]` 属性的定理。
使用 {leanRef}`simp only` 可以排除这些默认规则，从而允许你使用更精确制定的规则列表。
在下面的示例中，减号和 {leanRef}`only` 被用来阻止 {leanRef}`reverse_mk_symm` 的应用。

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```
:::

-- The {leanRef}`simp` tactic has many configuration options. For example, we can enable contextual simplifications as follows:
{leanRef}`simp` 策略有许多配置选项。例如，我们可以按如下方式启用上下文相关的化简：

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual
```

-- With {leanRef}`+contextual`, the {leanRef}`simp` tactic uses the fact that {leanRef}`x = 0` when simplifying {leanRef}`y + x = y`, and
-- {leanRef}`x ≠ 0` when simplifying the other branch. Here is another example:
使用 {leanRef}`+contextual` 时，{leanRef}`simp` 策略在化简 {leanRef}`y + x = y` 时会使用 {leanRef}`x = 0` 这一事实，
而在化简另一个分支时会使用 {leanRef}`x ≠ 0`。这里有另一个例子：

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual
```

:::leanFirst
-- Another useful configuration option is {leanRef}`+arith` which enables arithmetical simplifications.
另一个有用的配置选项是 {leanRef}`+arith`，它启用了算术化简。

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith
```
:::

-- # Split Tactic
# 分解策略 (Split Tactic)
%%%
tag := "split-tactic"
%%%

::::leanFirst

-- The {leanRef}`split` tactic is useful for breaking nested {kw}`if`-{kw}`then`-{kw}`else` and {kw}`match` expressions in cases.
-- For a {kw}`match` expression with $`n` cases, the {leanRef}`split` tactic generates at most $`n` subgoals. Here is an example:
{leanRef}`split` 策略对于将嵌套的 {kw}`if`-{kw}`then`-{kw}`else` 和 {kw}`match` 表达式分解为不同情况非常有用。
对于具有 $`n` 个分支的 {kw}`match` 表达式，{leanRef}`split` 策略最多生成 $`n` 个子目标。这里有一个例子：

```lean
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```
::::

-- We can compress the tactic proof above as follows.
我们可以将上面的策略证明压缩如下。

```lean
def f (x y z : Nat) : Nat :=
 match x, y, z with
 | 5, _, _ => y
 | _, 5, _ => y
 | _, _, 5 => y
 | _, _, _ => 1
------
example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

-- The tactic {leanRef}`split <;> first | contradiction | rfl` first applies the {leanRef}`split` tactic,
-- and then for each generated goal it tries {leanRef}`contradiction`, and then {leanRef}`rfl` if {leanRef}`contradiction` fails.
-- Like {leanRef}`simp`, we can apply {leanRef}`split` to a particular hypothesis:
策略 {leanRef}`split <;> first | contradiction | rfl` 首先应用 {leanRef}`split` 策略，
然后对于生成的每个目标，它尝试执行 {leanRef}`contradiction`，如果 {leanRef}`contradiction` 失败，则尝试执行 {leanRef}`rfl`。
与 {leanRef}`simp` 类似，我们可以将 {leanRef}`split` 应用于特定的假设：

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, _] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h
```

-- # Extensible Tactics
# 可扩展策略 (Extensible Tactics)
%%%
tag := "extensible-tactics"
%%%

:::leanFirst
-- In the following example, we define the notation {leanRef}`triv` using the command {leanRef}`syntax`.
-- Then, we use the command {leanRef}`macro_rules` to specify what should
-- be done when {leanRef}`triv` is used. You can provide different expansions, and the tactic
-- interpreter will try all of them until one succeeds:
在下面的示例中，我们使用 {leanRef}`syntax` 命令定义了记号 {leanRef}`triv`。
然后，我们使用 {leanRef}`macro_rules` 命令来指定在使用 {leanRef}`triv` 时应该执行的操作。
你可以提供不同的展开方式，策略解释器将尝试所有这些展开方式，直到其中一个成功为止：

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```
:::

-- # Exercises
# 练习
%%%
tag := "tactics-exercises"
%%%

-- 1. Go back to the exercises in {ref "propositions-and-proofs"}[Propositions and Proofs] and
-- {ref "quantifiers-and-equality"}[Quantifiers and Equality] and
-- redo as many as you can now with tactic proofs, using also {tactic}`rw`
-- and {tactic}`simp` as appropriate.
1. 回到 {ref "propositions-and-proofs"}[命题和证明] 和 {ref "quantifiers-and-equality"}[全称量词和等式] 中的练习，
现在尽可能多地使用策略证明来重做它们，并根据需要使用 {tactic}`rw` 和 {tactic}`simp`。

-- 2. Use tactic combinators to obtain a one-line proof of the following:
2. 使用策略组合器获得以下内容的一行证明：

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry
```
