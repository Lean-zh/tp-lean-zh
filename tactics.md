<!--
Tactics
=======
-->

证明策略
=======

<!--
In this chapter, we describe an alternative approach to constructing
proofs, using *tactics*.  A proof term is a representation of a
mathematical proof; tactics are commands, or instructions, that
describe how to build such a proof. Informally, you might begin a
mathematical proof by saying "to prove the forward direction, unfold
the definition, apply the previous lemma, and simplify." Just as these
are instructions that tell the reader how to find the relevant proof,
tactics are instructions that tell Lean how to construct a proof
term. They naturally support an incremental style of writing proofs,
in which you decompose a proof and work on goals one step at a time.

We will describe proofs that consist of sequences of tactics as
"tactic-style" proofs, to contrast with the ways of writing proof
terms we have seen so far, which we will call "term-style"
proofs. Each style has its own advantages and disadvantages. For
example, tactic-style proofs can be harder to read, because they
require the reader to predict or guess the results of each
instruction. But they can also be shorter and easier to
write. Moreover, tactics offer a gateway to using Lean's automation,
since automated procedures are themselves tactics.
-->

在本章中，我们描述了另一种构建证明的方法，即使用 **策略（Tactic）** 。 一个证明项代表一个数学证明；策略是描述如何建立这样一个证明的命令或指令。你可以在数学证明开始时非正式地说：「为了证明条件的必要性，展开定义，应用前面的定理，并进行简化。」就像这些指令告诉读者如何构建证明一样，策略告诉 Lean 如何构建证明。它们自然而然地支持增量式的证明书写，在这种写作方式中，你将分解一个证明，并一步步地实现目标。

> 译者注：tactic 和 strategy 都有策略的意思，其中 tactic 侧重细节，如排兵布阵，
> strategy 面向整体，如大规模战略。试译 strategy 为「要略」，与 tactic 相区分。

我们将把由策略序列组成的证明描述为「策略式」(tactic-style)证明，前几章的证明我们称为「项式」(term-style)证明。每种风格都有自己的优点和缺点。例如，项式证明可能更难读，因为它们要求读者预测或猜测每条指令的结果。但它们一般更短，更容易写。此外，策略提供了一个使用 Lean 自动化的途径，因为自动化程序本身就是策略。

<!--
Entering Tactic Mode
--------------------
-->

进入策略模式
--------------------

<!--
Conceptually, stating a theorem or introducing a ``have`` statement
creates a goal, namely, the goal of constructing a term with the
expected type. For example, the following creates the goal of
constructing a term of type ``p ∧ q ∧ p``, in a context with constants
``p q : Prop``, ``hp : p`` and ``hq : q``:
-->

从概念上讲，陈述一个定理或引入一个 ``have`` 的声明会产生一个目标，即构造一个具有预期类型的项的目标。例如, 下面创建的目标是构建一个类型为 ``p ∧ q ∧ p`` 的项，条件有常量 ``p q : Prop``，``hp : p`` 和 ``hq : q``。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry
```

<!--
You can write this goal as follows:
-->

写成目标如下：

```
    p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
```

<!--
Indeed, if you replace the "sorry" by an underscore in the example
above, Lean will report that it is exactly this goal that has been
left unsolved.

Ordinarily, you meet such a goal by writing an explicit term. But
wherever a term is expected, Lean allows us to insert instead a ``by
<tactics>`` block, where ``<tactics>`` is a sequence of commands,
separated by semicolons or line breaks. You can prove the theorem above
in that way:
-->

事实上，如果你把上面的例子中的「sorry」换成下划线，Lean 会报告说，正是这个目标没有得到解决。

通常情况下，你会通过写一个明确的项来满足这样的目标。但在任何需要项的地方，Lean 允许我们插入一个 ``by <tactics>`` 块，其中 ``<tactics>`` 是一串命令，用分号或换行符分开。你可以用下面这种方式来证明上面的定理：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

<!--
We often put the ``by`` keyword on the preceding line, and write the
example above as:
-->

我们经常将 ``by`` 关键字放在前一行，并将上面的例子写为

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

<!--
The ``apply`` tactic applies an expression, viewed as denoting a
function with zero or more arguments. It unifies the conclusion with
the expression in the current goal, and creates new goals for the
remaining arguments, provided that no later arguments depend on
them. In the example above, the command ``apply And.intro`` yields two
subgoals:
-->

``apply`` 策略应用于一个表达式，被视为表示一个有零或多个参数的函数。它将结论与当前目标中的表达式统一起来，并为剩余的参数创建新的目标，只要后面的参数不依赖于它们。在上面的例子中，命令 ``apply And.intro`` 产生了两个子目标：

```
    case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p

    case right
    p q : Prop
    hp : p
    hq : q
    ⊢ q ∧ p
```

<!--
The first goal is met with the command ``exact hp``. The ``exact``
command is just a variant of ``apply`` which signals that the
expression given should fill the goal exactly. It is good form to use
it in a tactic proof, since its failure signals that something has
gone wrong. It is also more robust than ``apply``, since the
elaborator takes the expected type, given by the target of the goal,
into account when processing the expression that is being applied. In
this case, however, ``apply`` would work just as well.

You can see the resulting proof term with the ``#print`` command:
-->

第一个目标是通过 ``exact hp`` 命令来实现的。``exact`` 命令只是 ``apply`` 的一个变体，它表示所给的表达式应该准确地填充目标。在策略证明中使用它很有益，因为它如果失败那么表明出了问题。它也比 ``apply`` 更稳健，因为繁饰器在处理被应用的表达式时，会考虑到目标所预期的类型。然而，在这种情况下，``apply`` 也可以很好地工作。

你可以用`#print`命令查看所产生的证明项。

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test
```

<!--
You can write a tactic script incrementally. In VS Code, you can open
a window to display messages by pressing ``Ctrl-Shift-Enter``, and
that window will then show you the current goal whenever the cursor is
in a tactic block. In Emacs, you can see the goal at the end of any
line by pressing ``C-c C-g``, or see the remaining goal in an
incomplete proof by putting the cursor after the first character of
the last tactic. If the proof is incomplete, the token ``by`` is
decorated with a red squiggly line, and the error message contains the
remaining goals.

Tactic commands can take compound expressions, not just single
identifiers. The following is a shorter version of the preceding
proof:
-->

你可以循序渐进地写一个策略脚本。在VS Code中，你可以通过按`Ctrl-Shift-Enter`打开一个窗口来显示信息，然后只要光标在策略块中，该窗口就会显示当前的目标。在 Emacs 中，你可以通过按`C-c C-g`看到任何一行末尾的目标，或者通过把光标放在最后一个策略的第一个字符之后，看到一个不完整的证明中的剩余目标。如果证明是不完整的，标记 ``by`` 会被装饰成一条红色的斜线，错误信息中包含剩余的目标。

策略命令可以接受复合表达式，而不仅仅是单一标识符。下面是前面证明的一个简短版本。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

<!--
Unsurprisingly, it produces exactly the same proof term.
-->

它产生了相同的证明项。

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro hp
#  exact And.intro hq hp
#print test
```

<!--
Multiple tactic applications can be written in a single line by concatenating with a semicolon.
-->

应用多个策略可以通过用分号连接写在一行中。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

<!--
Tactics that may produce multiple subgoals often tag them. For
example, the tactic ``apply And.intro`` tagged the first subgoal as
``left``, and the second as ``right``. In the case of the ``apply``
tactic, the tags are inferred from the parameters' names used in the
``And.intro`` declaration. You can structure your tactics using the
notation ``case <tag> => <tactics>``. The following is a structured
version of our first tactic proof in this chapter.
-->

可能产生多个子目标的策略通常对子目标进行标记。例如，``apply And.intro`` 策略将第一个目标标记为 ``left``，将第二个目标标记为 ``right``。在 ``apply`` 策略的情况下，标签是从 ``And.intro`` 声明中使用的参数名称推断出来的。你可以使用符号 ``case <tag> => <tactics>`` 来结构化你的策略。下面是本章中第一个策略证明的结构化版本。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

<!--
You can solve the subgoal ``right`` before ``left`` using the ``case``
notation:
-->

使用 ``case`` 标记，你也可以在 ``left`` 之前先解决子目标 ``right``：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

<!--
Note that Lean hides the other goals inside the ``case`` block. We say
it is "focusing" on the selected goal.  Moreover, Lean flags an error
if the selected goal is not fully solved at the end of the ``case``
block.

For simple subgoals, it may not be worth selecting a subgoal using its
tag, but you may still want to structure the proof. Lean also provides
the "bullet" notation ``. <tactics>`` (or ``· <tactics>``) for
structuring proof.
-->

注意，Lean 将其他目标隐藏在 ``case`` 块内。我们说它「专注」于选定的目标。 此外，如果所选目标在 ``case`` 块的末尾没有完全解决，Lean 会标记一个错误。

对于简单的子目标，可能不值得使用其标签来选择一个子目标，但你可能仍然想要结构化证明。Lean 还提供了「子弹」符号 ``. <tactics>`` 或 ``· <tactics>``。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

<!--
Basic Tactics
-------------
-->

基本策略
-------------

<!--
In addition to ``apply`` and ``exact``, another useful tactic is
``intro``, which introduces a hypothesis. What follows is an example
of an identity from propositional logic that we proved in a previous
chapter, now proved using tactics.
-->

除了 ``apply`` 和 ``exact`` 之外，另一个有用的策略是 ``intro``，它引入了一个假设。下面是我们在前一章中证明的命题逻辑中的一个等价性的例子，现在用策略来证明。

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

<!--
The ``intro`` command can more generally be used to introduce a variable of any type:
-->

``intro`` 命令可以更普遍地用于引入任何类型的变量。

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

<!--
You can use it to introduce several variables:
-->

你可以同时引入好几个变量：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

<!--
As the ``apply`` tactic is a command for constructing function
applications interactively, the ``intro`` tactic is a command for
constructing function abstractions interactively (i.e., terms of the
form ``fun x => e``).  As with lambda abstraction notation, the
``intro`` tactic allows us to use an implicit ``match``.
-->

由于 ``apply`` 策略是一个用于交互式构造函数应用的命令，``intro`` 策略是一个用于交互式构造函数抽象的命令（即 ``fun x => e`` 形式的项）。 与 lambda 抽象符号一样，``intro`` 策略允许我们使用隐式的 ``match``。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

<!--
You can also provide multiple alternatives like in the ``match`` expression.
-->

就像 ``match`` 表达式一样，你也可以提供多个选项。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

<!--
The ``intros`` tactic can be used without any arguments, in which
case, it chooses names and introduces as many variables as it can. You
will see an example of this in a moment.

The ``assumption`` tactic looks through the assumptions in context of
the current goal, and if there is one matching the conclusion, it
applies it.
-->

``intros`` 策略可以在没有任何参数的情况下使用，在这种情况下，它选择名字并尽可能多地引入变量。稍后你会看到一个例子。

``assumption`` 策略在当前目标的背景下查看假设，如果有一个与结论相匹配的假设，它就会应用这个假设。

<!--
```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```
-->

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- 应用h₃
```

<!--
It will unify metavariables in the conclusion if necessary:
-->

若有必要，它会在结论中统一元变量。

<!--
```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```
-->

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- 求解了 x = ?b with h₁
  apply Eq.trans
  assumption      -- 求解了 y = ?h₂.b with h₂
  assumption      -- 求解了 z = w with h₃
```

<!--
The following example uses the ``intros`` command to introduce the three variables and two hypotheses automatically:
-->

下面的例子使用 ``intros`` 命令来自动引入三个变量和两个假设：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```

<!--
Note that names automatically generated by Lean are inaccessible by default. The motivation is to
ensure your tactic proofs do not rely on automatically generated names, and are consequently more robust.
However, you can use the combinator ``unhygienic`` to disable this restriction.
-->

请注意，由 Lean 自动生成的名称在默认情况下是不可访问的。其动机是为了确保你的策略证明不依赖于自动生成的名字，并因此而更加强大。然而，你可以使用组合器 ``unhygienic`` 来禁用这一限制。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

<!--
You can also use the ``rename_i`` tactic to rename the most recent inaccessible names in your context.
In the following example, the tactic ``rename_i h1 _ h2`` renames two of the last three hypotheses in
your context.
-->

你也可以使用 ``rename_i`` 策略来重命名你的上下文中最近的不能访问的名字。在下面的例子中，策略 ``rename_i h1 _ h2`` 在你的上下文中重命名了三个假设中的两个。

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```

<!--
The ``rfl`` tactic is syntactic sugar for ``exact rfl``.
-->

``rfl`` 策略是 ``exact rfl`` 的语法糖。

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl
```

<!--
The ``repeat`` combinator can be used to apply a tactic several times.
-->

``repeat`` 组合器可以多次使用一个策略。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

<!--
Another tactic that is sometimes useful is the ``revert`` tactic,
which is, in a sense, an inverse to ``intro``.
-->

另一个有时很有用的策略是还原 ``revert`` 策略，从某种意义上说，它是对 ``intro`` 的逆。

```lean
example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

<!--
Moving a hypothesis into the goal yields an implication:
-->

将一个假设还原到目标中会产生一个蕴含。

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

<!--
But ``revert`` is even more clever, in that it will revert not only an
element of the context but also all the subsequent elements of the
context that depend on it. For example, reverting ``x`` in the example
above brings ``h`` along with it:
-->

但是 `revert` 更聪明，因为它不仅会还原上下文中的一个元素，还会还原上下文中所有依赖它的后续元素。例如，在上面的例子中，还原 `x` 会带来 `h`。

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

<!--
You can also revert multiple elements of the context at once:
-->

你还可以一次性还原多个元素：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

<!--
You can only ``revert`` an element of the local context, that is, a
local variable or hypothesis. But you can replace an arbitrary
expression in the goal by a fresh variable using the ``generalize``
tactic.
-->

你只能 ``revert`` 局部环境中的一个元素，也就是一个局部变量或假设。但是你可以使用泛化 ``generalize`` 策略将目标中的任意表达式替换为新的变量。

```lean
example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

<!--
The mnemonic in the notation above is that you are generalizing the
goal by setting ``3`` to an arbitrary variable ``x``. Be careful: not
every generalization preserves the validity of the goal. Here,
``generalize`` replaces a goal that could be proved using
``rfl`` with one that is not provable:
-->

上述符号的记忆法是，你通过将 ``3`` 设定为任意变量 ``x`` 来泛化目标。要注意：不是每一个泛化都能保留目标的有效性。这里，`generalize` 用一个无法证明的目标取代了一个可以用 ``rfl`` 证明的目标。

```lean
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
```

<!--
In this example, the ``admit`` tactic is the analogue of the ``sorry``
proof term. It closes the current goal, producing the usual warning
that ``sorry`` has been used. To preserve the validity of the previous
goal, the ``generalize`` tactic allows us to record the fact that
``3`` has been replaced by ``x``. All you need to do is to provide a
label, and ``generalize`` uses it to store the assignment in the local
context:
-->

在这个例子中，``admit`` 策略是 ``sorry`` 证明项的类似物。它关闭了当前的目标，产生了通常的警告：使用了 ``sorry``。为了保持之前目标的有效性，`generalize` 策略允许我们记录 `3` 已经被 `x` 所取代的事实。你所需要做的就是提供一个标签，`generalize` 使用它来存储局部上下文中的赋值。

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

<!--
Here the ``rewrite`` tactic, abbreviated ``rw``, uses ``h`` to replace
``x`` by ``3`` again. The ``rewrite`` tactic will be discussed below.
-->

这里 ``rewrite`` 策略，缩写为 ``rw``，用 ``h`` 把 ``x`` 用 ``3`` 换了回来。``rewrite`` 策略下文将继续讨论。

<!--
More Tactics
------------
-->

更多策略
------------

<!--
Some additional tactics are useful for constructing and destructing
propositions and data. For example, when applied to a goal of the form
``p ∨ q``, you use tactics such as ``apply Or.inl`` and ``apply
Or.inr``.  Conversely, the ``cases`` tactic can be used to decompose a
disjunction.
-->

一些额外的策略对于建构和析构命题以及数据很有用。例如，当应用于形式为 ``p ∨ q`` 的目标时，你可以使用 ``apply Or.inl`` 和 ``apply Or.inr`` 等策略。 反之，``cases`` 策略可以用来分解一个析取。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

<!--
Note that the syntax is similar to the one used in `match` expressions.
The new subgoals can be solved in any order.
-->

注意，该语法与 `match` 表达式中使用的语法相似。新的子目标可以按任何顺序解决。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

<!--
You can also use a (unstructured) ``cases`` without the ``with`` and a tactic
for each alternative.
-->

你也可以使用一个（非结构化的）`cases`，而不使用 `with`，并为每个备选情况制定一个策略。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

<!--
The (unstructured) ``cases`` is particularly useful when you can close several
subgoals using the same tactic.
-->

（非结构化的）`cases` 在你可以用同一个策略来解决子任务时格外有用。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

<!--
You can also use the combinator ``tac1 <;> tac2`` to apply ``tac2`` to each
subgoal produced by tactic ``tac1``.
-->

你也可以使用组合器 ``tac1 <;> tac2``，将 ``tac2`` 应用于策略 ``tac1`` 产生的每个子目标。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

<!--
You can combine the unstructured ``cases`` tactic with the ``case`` and ``.`` notation.
-->

你可以与 ``.`` 符号相结合使用非结构化的 ``cases`` 策略。

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

<!--
The ``cases`` tactic can also be used to
decompose a conjunction.
-->

``cases`` 策略也被用来分解一个析取。

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
```

<!--
In this example, there is only one goal after the ``cases`` tactic is
applied, with ``h : p ∧ q`` replaced by a pair of assumptions,
``hp : p`` and ``hq : q``. The ``constructor`` tactic applies the unique
constructor for conjunction, ``And.intro``. With these tactics, an
example from the previous section can be rewritten as follows:
-->

在这个例子中，应用 ``cases`` 策略后只有一个目标，``h : p ∧ q`` 被一对假设取代，``hp : p`` 和 ``hq : q``。``constructor`` 策略应用了唯一一个合取构造子 ``And.intro``。有了这些策略，上一节的一个例子可以改写如下。

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
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr
```

<!--
You will see in [Chapter Inductive Types](./inductive_types.md) that
these tactics are quite general. The ``cases`` tactic can be used to
decompose any element of an inductively defined type; ``constructor``
always applies the first applicable constructor of an inductively defined type.
For example, you can use ``cases`` and ``constructor`` with an existential quantifier:
-->

你将在[归纳类型](./inductive_types.md)一章中看到，这些策略是相当通用的。``cases`` 策略可以用来分解递归定义类型的任何元素；``constructor`` 总是应用递归定义类型的第一个适用构造子。例如，你可以使用 ``cases`` 和 ``constructor`` 与一个存在量词：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

<!--
Here, the ``constructor`` tactic leaves the first component of the
existential assertion, the value of ``x``, implicit. It is represented
by a metavariable, which should be instantiated later on. In the
previous example, the proper value of the metavariable is determined
by the tactic ``exact px``, since ``px`` has type ``p x``. If you want
to specify a witness to the existential quantifier explicitly, you can
use the ``exists`` tactic instead:
-->

在这里，``constructor`` 策略将存在性断言的第一个组成部分，即 ``x`` 的值，保留为隐式的。它是由一个元变量表示的，这个元变量以后应该被实例化。在前面的例子中，元变量的正确值是由策略 ``exact px`` 决定的，因为 ``px`` 的类型是 ``p x``。如果你想明确指定存在量词的存在者，你可以使用 `exists` 策略来代替。

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

<!--
Here is another example:
-->

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

<!--
These tactics can be used on data just as well as propositions. In the
next example, they are used to define functions which swap the
components of the product and sum types:
-->

这些策略既可以用在命题上，也可以用在数上。在下面的两个例子中，它们被用来定义交换乘法和加法类型组件的函数：

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

<!--
Note that up to the names we have chosen for the variables, the
definitions are identical to the proofs of the analogous propositions
for conjunction and disjunction. The ``cases`` tactic will also do a
case distinction on a natural number:
-->

在我们为变量选择的名称之前，它们的定义与有关合取和析取的类似命题的证明是相同的。``cases`` 策略也会对自然数进行逐情况区分：

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

<!--
The ``cases`` tactic, and its companion, the ``induction`` tactic, are discussed in greater detail in
the [Tactics for Inductive Types](./inductive_types.md#tactics-for-inductive-types) section.

The ``contradiction`` tactic searches for a contradiction among the hypotheses of the current goal:
-->

``cases`` 策略伙同 ``induction`` 策略将在[归纳类型的策略](./inductive_types.md#_tactics_for_inductive_types)一节中详述。

``contradiction`` 策略搜索当前目标的假设中的矛盾：

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

<!--
You can also use ``match`` in tactic blocks.
-->

你也可以在策略块中使用 ``match``：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
```

<!--
You can "combine" ``intro h`` with ``match h ...`` and write the previous examples as follows
-->

你可以将 ``intro h`` 与 ``match h ...`` 结合起来，然后上例就可以如下地写出：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption
```

<!--
Structuring Tactic Proofs
-------------------------
-->

结构化策略证明
-------------------------

<!--
Tactics often provide an efficient way of building a proof, but long
sequences of instructions can obscure the structure of the
argument. In this section, we describe some means that help provide
structure to a tactic-style proof, making such proofs more readable
and robust.

One thing that is nice about Lean's proof-writing syntax is that it is
possible to mix term-style and tactic-style proofs, and pass between
the two freely. For example, the tactics ``apply`` and ``exact``
expect arbitrary terms, which you can write using ``have``, ``show``,
and so on. Conversely, when writing an arbitrary Lean term, you can
always invoke the tactic mode by inserting a ``by``
block. The following is a somewhat toy example:
-->

策略通常提供了建立证明的有效方法，但一长串指令会掩盖论证的结构。在这一节中，我们将描述一些有助于为策略式证明提供结构的方法，使这种证明更易读，更稳健。

Lean 的证明写作语法的一个优点是，它可以混合项式和策略式证明，并在两者之间自由转换。例如，策略 ``apply`` 和 ``exact`` 可以传入任意的项，你可以用 ``have``，``show`` 等等来写这些项。反之，当写一个任意的 Lean 项时，你总是可以通过插入一个 ``by`` 块来调用策略模式。下面是一个简易例子：

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

<!--
The following is a more natural example:
-->

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

<!--
In fact, there is a ``show`` tactic, which is similar to the
``show`` expression in a proof term. It simply declares the type of the
goal that is about to be solved, while remaining in tactic
mode.
-->

事实上，有一个 ``show`` 策略，它类似于证明项中的 ``show`` 表达式。它只是简单地声明即将被解决的目标的类型，同时保持策略模式。

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

<!--
The ``show`` tactic can actually be used to rewrite a goal to something definitionally equivalent:
-->

``show`` 策略其实可以被用来重写一些定义等价的目标：

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

<!--
There is also a ``have`` tactic, which introduces a new subgoal, just as when writing proof terms:
-->

还有一个 ``have`` 策略，它引入了一个新的子目标，就像写证明项时一样。

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

<!--
As with proof terms, you can omit the label in the ``have`` tactic, in
which case, the default label ``this`` is used:
-->

与证明项一样，你可以省略 ``have`` 策略中的标签，在这种情况下，将使用默认标签 ``this``：

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

<!--
The types in a ``have`` tactic can be omitted, so you can write ``have
hp := h.left`` and ``have hqr := h.right``.  In fact, with this
notation, you can even omit both the type and the label, in which case
the new fact is introduced with the label ``this``.
-->

``have`` 策略中的类型可以省略，所以你可以写 ``have hp := h.left`` 和 ``have hqr := h.right``。 事实上，使用这种符号，你甚至可以省略类型和标签，在这种情况下，新的事实是用标签 ``this`` 引入的。

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

<!--
Lean also has a ``let`` tactic, which is similar to the ``have``
tactic, but is used to introduce local definitions instead of
auxiliary facts. It is the tactic analogue of a ``let`` in a proof
term.
-->

Lean 还有一个 ``let`` 策略，与 ``have`` 策略类似，但用于引入局部定义而不是辅助事实。它是证明项中 ``let`` 的策略版。

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

<!--
As with ``have``, you can leave the type implicit by writing ``let a
:= 3 * 2``. The difference between ``let`` and ``have`` is that
``let`` introduces a local definition in the context, so that the
definition of the local declaration can be unfolded in the proof.

We have used ``.`` to create nested tactic blocks.  In a nested block,
Lean focuses on the first goal, and generates an error if it has not
been fully solved at the end of the block. This can be helpful in
indicating the separate proofs of multiple subgoals introduced by a
tactic. The notation ``.`` is whitespace sensitive and relies on the indentation
to detect whether the tactic block ends. Alternatively, you can
define tactic blocks using curly braces and semicolons.
-->

和 ``have`` 一样，你可以通过写 ``let a := 3 * 2`` 来保留类型为隐式。``let`` 和 ``have`` 的区别在于，``let`` 在上下文中引入了一个局部定义，因此局部声明的定义可以在证明中展开。

我们使用了`.`来创建嵌套的策略块。 在一个嵌套块中，Lean 专注于第一个目标，如果在该块结束时还没有完全解决，就会产生一个错误。这对于表明一个策略所引入的多个子目标的单独证明是有帮助的。符号 ``.`` 是对空格敏感的，并且依靠缩进来检测策略块是否结束。另外，你也可以用大括号和分号来定义策略块。

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

<!--
It is useful to use indentation to structure proof: every time a tactic
leaves more than one subgoal, we separate the remaining subgoals by
enclosing them in blocks and indenting.  Thus if the application of
theorem ``foo`` to a single goal produces four subgoals, one would
expect the proof to look like this:
-->

使用缩进来构造证明很有用：每次一个策略留下一个以上的子目标时，我们通过将它们封装在块中并缩进来分隔剩下的子目标。因此，如果将定理 ``foo`` 应用于一个目标产生了四个子目标，那么我们就可以期待这样的证明：

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

<!--
or
-->

或

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

<!--
or
-->

或

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

<!--
Tactic Combinators
------------------
-->

策略组合器
------------------

<!--
*Tactic combinators* are operations that form new tactics from old
ones. A sequencing combinator is already implicit in the ``by`` block:
-->

 **策略组合器** 是由旧策略形成新策略的操作。``by`` 隐含了一个序列组合器：

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

<!--
Here, ``apply Or.inl; assumption`` is functionally equivalent to a
single tactic which first applies ``apply Or.inl`` and then applies
``assumption``.

In ``t₁ <;> t₂``, the ``<;>`` operator provides a *parallel* version of the sequencing operation:
``t₁`` is applied to the current goal, and then ``t₂`` is applied to *all* the resulting subgoals:
-->

这里，`apply Or.inl; assumption`在功能上等同于一个单独的策略，它首先应用`apply Or.inl`，然后应用 `assumption`。

在`t₁ <;> t₂`中，`<;>`操作符提供了一个*并行*的序列操作。`t₁`被应用于当前目标，然后`t₂`被应用于*所有*产生的子目标：

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

<!--
This is especially useful when the resulting goals can be finished off
in a uniform way, or, at least, when it is possible to make progress
on all of them uniformly.

The ``first | t₁ | t₂ | ... | tₙ`` applies each `tᵢ` until one succeeds, or else fails:
-->

当所产生的目标能够以统一的方式完成时，或者，至少，当有可能以统一的方式在所有的目标上取得进展时，这就特别有用。

``first | t₁ | t₂ | ... | tₙ`` 应用每$1 $2，直到其中一个成功，否则就失败：

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

<!--
In the first example, the left branch succeeds, whereas in the second one, it is the right one that succeeds.
In the next three examples, the same compound tactic succeeds in each case.
-->

在第一个例子中，左分支成功了，而在第二个例子中，右分支成功了。在接下来的三个例子中，同样的复合策略在每种情况下都能成功。

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

<!--
The tactic tries to solve the left disjunct immediately by assumption;
if that fails, it tries to focus on the right disjunct; and if that
doesn't work, it invokes the assumption tactic.

You will have no doubt noticed by now that tactics can fail. Indeed,
it is the "failure" state that causes the *first* combinator to
backtrack and try the next tactic. The ``try`` combinator builds a
tactic that always succeeds, though possibly in a trivial way:
``try t`` executes ``t`` and reports success, even if ``t`` fails. It is
equivalent to ``first | t | skip``, where ``skip`` is a tactic that does
nothing (and succeeds in doing so). In the next example, the second
``constructor`` succeeds on the right conjunct ``q ∧ r`` (remember that
disjunction and conjunction associate to the right) but fails on the
first. The ``try`` tactic ensures that the sequential composition
succeeds.
-->

该策略试图通过假设立即解决左边的析取项；如果失败，它就试图关注右边的析取项；如果不成功，它就调用假设策略。

毫无疑问，策略可能会失败。事实上，正是这种「失败」状态导致 `first` 组合器回溯并尝试下一个策略。``try`` 组合器建立了一个总是成功的策略，尽管可能是以一种平凡的方式：``try t`` 执行 ``t`` 并报告成功，即使 ``t`` 失败。它等同于 ``first | t | skip``，其中 ``skip`` 是一个什么都不做的策略（并且成功地做到了「什么都不做」）。在下一个例子中，第二个 `constructor` 在右边的合取项 ``q ∧ r`` 上成功了（注意，合取和析取是右结合的），但在第一个合取项上失败。`try` 策略保证了序列组合的成功。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

<!--
Be careful: ``repeat (try t)`` will loop forever, because the inner tactic never fails.

In a proof, there are often multiple goals outstanding. Parallel
sequencing is one way to arrange it so that a single tactic is applied
to multiple goals, but there are other ways to do this. For example,
``all_goals t`` applies ``t`` to all open goals:
-->

小心：``repeat (try t)`` 将永远循环，因为内部策略永远不会失败。

在一个证明中，往往有多个目标未完成。并行序列是一种布置方式，以便将一个策略应用于多个目标，但也有其他的方式可以做到这一点。例如，`all_goals t`将 `t` 应用于所有未完成的目标：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

<!--
In this case, the ``any_goals`` tactic provides a more robust solution.
It is similar to ``all_goals``, except it succeeds if its argument
succeeds on at least one goal.
-->

在这种情况下，``any_goals`` 策略提供了一个更稳健的解决方案。它与 ``all_goals`` 类似，只是除非它的参数至少在一个目标上成功，否则就会失败。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

<!--
The first tactic in the ``by`` block below repeatedly splits
conjunctions:
-->

下面 ``by`` 块中的第一个策略是反复拆分合取：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

<!--
In fact, we can compress the full tactic down to one line:
-->

其实可以将整个策略压缩成一行：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

<!--
The combinator ``focus t`` ensures that ``t`` only effects the current
goal, temporarily hiding the others from the scope. So, if ``t``
ordinarily only effects the current goal, ``focus (all_goals t)`` has
the same effect as ``t``.
-->

组合器 ``focus t`` 确保 ``t`` 只影响当前的目标，暂时将其他目标从作用范围中隐藏。因此，如果 `t` 通常只影响当前目标，`focus (all_goals t)`与 `t` 具有相同的效果。

<!--
Rewriting
---------
-->

重写
---------

<!--
The ``rewrite`` tactic (abbreviated ``rw``) and the ``simp`` tactic
were introduced briefly in [Calculational Proofs](./quantifiers_and_equality.md#calculational-proofs). In this
section and the next, we discuss them in greater detail.

The ``rewrite`` tactic provides a basic mechanism for applying
substitutions to goals and hypotheses, providing a convenient and
efficient way of working with equality. The most basic form of the
tactic is ``rewrite [t]``, where ``t`` is a term whose type asserts an
equality. For example, ``t`` can be a hypothesis ``h : x = y`` in the
context; it can be a general lemma, like
``add_comm : ∀ x y, x + y = y + x``, in which the rewrite tactic tries to find suitable
instantiations of ``x`` and ``y``; or it can be any compound term
asserting a concrete or general equation. In the following example, we
use this basic form to rewrite the goal using a hypothesis.
-->

在[计算式证明](./quantifiers_and_equality.md#计算式证明)一节中简要介绍了 ``rewrite`` 策略（简称 ``rw``）和 ``simp`` 策略。在本节和下一节中，我们将更详细地讨论它们。

``rewrite`` 策略提供了一种基本的机制，可以将替换应用于目标和假设，在处理等式时非常方便。该策略的最基本形式是 ``rewrite [t]``，其中 ``t`` 是一个类型断定为等式的项。例如，`t` 可以是上下文中的一个假设`h : x = y`；可以是一个一般的法则，如`add_comm : ∀ x y, x + y = y + x`，在这个法则中，重写策略试图找到 `x` 和 `y` 的合适实例；或者可以是任何断言具体或一般等式的复合项。在下面的例子中，我们使用这种基本形式，用一个假设重写目标。

<!--
```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```
-->

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- 用 0 换掉 k
  rw [h₁] -- 用 0 换掉 f 0
```

<!--
In the example above, the first use of ``rw`` replaces ``k`` with
``0`` in the goal ``f k = 0``. Then, the second one replaces ``f 0``
with ``0``. The tactic automatically closes any goal of the form
``t = t``. Here is an example of rewriting using a compound expression:
-->

在上面的例子中，第一次使用 ``rw`` 将目标 ``f k = 0`` 中的 ``k`` 替换成 ``0``。然后，第二次用 ``0`` 替换 ``f 0``。该策略自动关闭任何形式的目标`t = t`。下面是一个使用复合表达式进行重写的例子。

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

<!--
Here, ``h hq`` establishes the equation ``x = y``.

Multiple rewrites can be combined using the notation ``rw [t_1, ..., t_n]``,
which is just shorthand for ``rw [t_1]; ...; rw [t_n]``. The previous example can be written as follows:
-->

这里，``h hq`` 建立了等式 ``x = y``。``h hq`` 周围的括号是不必要的，但为了清楚起见，还是加上了括号。

多个重写可以使用符号`rw [t_1, ..., t_n]`来组合，这只是`rw t_1; ...; rw t_n`的缩写。前面的例子可以写成如下：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

<!--
By default, ``rw`` uses an equation in the forward direction, matching
the left-hand side with an expression, and replacing it with the
right-hand side. The notation ``←t`` can be used to instruct the
tactic to use the equality ``t`` in the reverse direction.
-->

默认情况下，``rw`` 正向使用一个等式，用一个表达式匹配左边的等式，然后用右边的等式替换它。符号 ``←t`` 可以用来指示策略在反方向上使用等式 ``t``。

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

<!--
In this example, the term ``←h₁`` instructs the rewriter to replace
``b`` with ``a``. In the editors, you can type the backwards arrow as
``\l``. You can also use the ascii equivalent, ``<-``.

Sometimes the left-hand side of an identity can match more than one
subterm in the pattern, in which case the ``rw`` tactic chooses the
first match it finds when traversing the term. If that is not the one
you want, you can use additional arguments to specify the appropriate
subterm.
-->

在这个例子中，项 ``←h₁`` 指示重写器用 ``a`` 替换 ``b``。在编辑器中，你可以用 ``\l`` 输入反箭头。你也可以使用 ascii 替代品 ``<-``。

有时一个等式的左侧可以匹配模式中的多个子项，在这种情况下，``rw`` 策略会在遍历项时选择它发现的第一个匹配。如果这不是你想要的，你可以使用附加参数来指定适当的子项。

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

<!--
In the first example above, the first step rewrites ``a + b + c`` to
``a + (b + c)``. The next step applies commutativity to the term
``b + c``; without specifying the argument, the tactic would instead rewrite
``a + (b + c)`` to ``(b + c) + a``. Finally, the last step applies
associativity in the reverse direction, rewriting ``a + (c + b)`` to
``a + c + b``. The next two examples instead apply associativity to
move the parenthesis to the right on both sides, and then switch ``b``
and ``c``. Notice that the last example specifies that the rewrite
should take place on the right-hand side by specifying the second
argument to ``Nat.add_comm``.

By default, the ``rewrite`` tactic affects only the goal. The notation
``rw [t] at h`` applies the rewrite ``t`` at hypothesis ``h``.
-->

在上面的第一个例子中，第一步将 ``a + b + c`` 重写为 ``a + (b + c)``。然后，接下来对项 ``b + c`` 使用交换律；如果不指定参数，该策略将把 ``a + (b + c)`` 重写为 ``(b + c) + a``。最后一步以相反的方向应用结合律，将`a + (c + b)`改写为 ``a + c + b``。接下来的两个例子则是应用结合律将两边的小括号移到右边，然后将 ``b`` 和 ``c`` 调换。注意最后一个例子通过指定 ``Nat.add_comm`` 的第二个参数来指定重写应该在右侧进行。

默认情况下，``rewrite`` 策略只影响目标。符号 ``rw [t] at h`` 在假设 ``h`` 处应用重写 ``t``。

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

<!--
The first step, ``rw [Nat.add_zero] at h``, rewrites the hypothesis ``a + 0 = 0`` to ``a = 0``.
Then the new hypothesis ``a = 0`` is used to rewrite the goal to ``f 0 = f 0``.

The ``rewrite`` tactic is not restricted to propositions.
In the following example, we use ``rw [h] at t`` to rewrite the hypothesis ``t : Tuple α n`` to ``t : Tuple α 0``.
-->

第一步，``rw [Nat.add_zero] at h`` 将假设 ``a + 0 = 0`` 改写为 ``a = 0``。然后，新的假设`a = 0`被用来把目标重写为`f 0 = f 0`。

``rewrite`` 策略不限于命题。在下面的例子中，我们用`rw [h] at t`来重写假设`t : Tuple α n`为`t : Tuple α 0`。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```

<!--
Using the Simplifier
--------------------
-->

简化
--------------------

<!--
Whereas ``rewrite`` is designed as a surgical tool for manipulating a
goal, the simplifier offers a more powerful form of automation. A
number of identities in Lean's library have been tagged with the
``[simp]`` attribute, and the ``simp`` tactic uses them to iteratively
rewrite subterms in an expression.
-->

``rewrite`` 被设计为操纵目标的手术刀，而简化器提供了一种更强大的自动化形式。Lean 库中的一些特性已经被标记为`[simp]`属性，`simp` 策略使用它们来反复重写表达式中的子项。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

<!--
In the first example, the left-hand side of the equality in the goal
is simplified using the usual identities involving 0 and 1, reducing
the goal to ``x * y = x * y``. At that point, ``simp`` applies
reflexivity to finish it off. In the second example, ``simp`` reduces
the goal to ``p (x * y)``, at which point the assumption ``h``
finishes it off. Here are some more examples
with lists:
-->

在第一个例子中，目标中等式的左侧被简化，使用涉及0和1的通常的同义词，将目标简化为`x * y = x * y'`。此时`simp'`应用反身性（rfl）来完成它。在第二个例子中，`simp` 将目标化简为`p (x * y)`，这时假设 `h` 完成了它。下面是一些关于列表的例子。

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

<!--
As with ``rw``, you can use the keyword ``at`` to simplify a hypothesis:
-->

就像 ``rw``，你也可以用关键字 ``at`` 来简化一个假设：

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

<!--
Moreover, you can use a "wildcard" asterisk to simplify all the hypotheses and the goal:
-->

此外，你可以使用一个「通配符」星号来简化所有的假设和目标：

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

<!--
For operations that are commutative and associative, like
multiplication on the natural numbers, the simplifier uses these two
facts to rewrite an expression, as well as *left commutativity*. In
the case of multiplication the latter is expressed as follows:
``x * (y * z) = y * (x * z)``. The ``local`` modifier tells the simplifier
to use these rules in the current file (or section or namespace, as
the case may be). It may seem that commutativity and
left-commutativity are problematic, in that repeated application of
either causes looping. But the simplifier detects identities that
permute their arguments, and uses a technique known as *ordered
rewriting*. This means that the system maintains an internal ordering
of terms, and only applies the identity if doing so decreases the
order. With the three identities mentioned above, this has the effect
that all the parentheses in an expression are associated to the right,
and the expressions are ordered in a canonical (though somewhat
arbitrary) way. Two expressions that are equivalent up to
associativity and commutativity are then rewritten to the same
canonical form.
-->

上例中前两行的意思是，对于具有交换律和结合律的运算（如自然数的加法和乘法），简化器使用这两个定律来重写表达式，同时还使用*左交换律*。在乘法的情况下，左交换律表达如下：``x * (y * z) = y * (x * z)``。`local` 修饰符告诉简化器在当前文件（或小节或命名空间，视情况而定）中使用这些规则。交换律和左交换律是有一个问题是，重复应用其中一个会导致循环。但是简化器检测到了对其参数进行置换的特性，并使用了一种被称为*有序重写*的技术。这意味着系统保持着项的内部次序，只有在这样做会降低次序的情况下才会应用等式。对于上面提到的三个等式，其效果是表达式中的所有小括号都被结合到右边，并且表达式以一种规范的（尽管有些随意）方式排序。两个在交换律和结合律上等价的表达式然后被改写成相同的规范形式。

```lean
# attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
# attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

<!--
As with ``rewrite``, you can send ``simp`` a list of facts to use,
including general lemmas, local hypotheses, definitions to unfold, and
compound expressions. The ``simp`` tactic also recognizes the ``←t``
syntax that ``rewrite`` does. In any case, the additional rules are
added to the collection of identities that are used to simplify a
term.
-->

与 ``rewrite`` 一样，你可以向 ``simp`` 提供一个要使用的事实列表，包括一般引理、局部假设、要展开的定义和复合表达式。`simp` 策略也能识别 `rewrite` 的`←t`语法。在任何情况下，额外的规则都会被添加到用于简化项的等式集合中。

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

<!--
A common idiom is to simplify a goal using local hypotheses:
-->

一个常见的习惯是用局部假设来简化一个目标：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

<!--
To use all the hypotheses present in the local context when
simplifying, we can use the wildcard symbol, ``*``:
-->

为了在简化时使用局部环境中存在的所有假设，我们可以使用通配符 ``*``：

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```

<!--
Here is another example:
-->

另一例：

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

<!--
The simplifier will also do propositional rewriting. For example,
using the hypothesis ``p``, it rewrites ``p ∧ q`` to ``q`` and ``p ∨
q`` to ``true``, which it then proves trivially. Iterating such
rewrites produces nontrivial propositional reasoning.
-->

简化器也会进行命题重写。例如，使用假设 ``p``，它把 ``p ∧ q`` 改写为 ``q``，把 ``p ∨ q`` 改写为 ``true``，然后以普通方式证明。迭代这样的重写，会生成非平凡的命题推理。

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

<!--
The next example simplifies all the hypotheses, and then uses them to prove the goal.
-->

下一个例子简化了所有的假设，然后用这些假设来证明目标。

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

<!--
One thing that makes the simplifier especially useful is that its
capabilities can grow as a library develops. For example, suppose we
define a list operation that symmetrizes its input by appending its
reversal:
-->

使得简化器特别有用的一点是，它的能力可以随着规则库的发展而增强。例如，假设我们定义了一个列表操作，该操作通过拼接其反转来对称其输入：

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

<!--
Then for any list ``xs``, ``reverse (mk_symm xs)`` is equal to ``mk_symm xs``,
which can easily be proved by unfolding the definition:
-->

那么对于任何列表 ``xs``，``reverse (mk_symm xs)`` 等于 ``mk_symm xs``，这可以通过展开定义轻松证明：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

<!--
We can now use this theorem to prove new results:
-->

你可以使用这个定理来证明一些新结果：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
# theorem reverse_mk_symm (xs : List α)
#        : (mk_symm xs).reverse = mk_symm xs := by
#  simp [mk_symm]
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

<!--
But using ``reverse_mk_symm`` is generally the right thing to do, and
it would be nice if users did not have to invoke it explicitly. You can
achieve that by marking it as a simplification rule when the theorem
is defined:
-->

但是使用 `reverse_mk_symm` 通常是正确的，如果用户不需要明确地调用它，那就更好了。你可以通过在定义该定理时将其标记为简化规则来实现这一点：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
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

<!--
The notation ``@[simp]`` declares ``reverse_mk_symm`` to have the
``[simp]`` attribute, and can be spelled out more explicitly:
-->

符号 ``@[simp]`` 声明 ``reverse_mk_symm`` 具有 ``[simp]`` 属性，可以更明确地说明：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
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

<!--
The attribute can also be applied any time after the theorem is declared:
-->

该属性也可以在定理声明后的任何时候应用：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
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

<!--
Once the attribute is applied, however, there is no way to permanently
remove it; it persists in any file that imports the one where the
attribute is assigned. As we will discuss further in
[Attributes](./interacting_with_lean.md#attributes), one can limit the scope of an attribute to the
current file or section using the ``local`` modifier:
-->

然而，一旦属性被应用，就没有办法永久地删除它；它将在任何导入该属性的文件中持续存在。正如我们将在[属性](./interacting_with_lean.md#属性)一章中进一步讨论的那样，我们可以使用 ``local`` 修饰符将属性的范围限制在当前文件或章节中：

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
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

<!--
Outside the section, the simplifier will no longer use
``reverse_mk_symm`` by default.

Note that the various ``simp`` options we have discussed --- giving an
explicit list of rules, and using ``at`` to specify the location --- can be combined,
but the order they are listed is rigid. You can see the correct order
in an editor by placing the cursor on the ``simp`` identifier to see
the documentation string that is associated with it.

There are two additional modifiers that are useful. By default,
``simp`` includes all theorems that have been marked with the
attribute ``[simp]``. Writing ``simp only`` excludes these defaults,
allowing you to use a more explicitly crafted list of
rules. In the examples below, the minus sign and
``only`` are used to block the application of ``reverse_mk_symm``.
-->

在该部分之外，简化器将不再默认使用 ``reverse_mk_symm``。

请注意，我们讨论过的各种 `simp` 选项----给出一个明确的规则列表，并使用 `at` 指定位置----可以合并，但它们的排列顺序是严格的。你可以在编辑器中看到正确的顺序，把光标放在 ``simp`` 标识符上，查看与之相关的文档。

有两个额外的修饰符是有用的。默认情况下，``simp`` 包括所有被标记为 ``[simp]`` 属性的定理。写`simp only`排除了这些默认值，允许你使用一个更明确的规则列表。在下面的例子中，减号和 ``only`` 被用来阻止 ``reverse_mk_symm`` 的应用：

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

<!--
The `simp` tactic has many configuration options. For example, we can enable contextual simplifications as follows.
-->

`simp` 策略有很多配置选项，例如，我们可以启用语境简化：

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })
```

<!--
when `contextual := true`, `simp` uses the fact that `x = 0` when simplifying `y + x = y`, and
`x ≠ 0` when simplifying the other branch. Here is another example.
-->

当`contextual := true`，`simp` 简化`y + x = y`时会使用`x = 0`，同时会用`x ≠ 0`来简化另一侧。另一个例子：

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp (config := { contextual := true })
```

<!--
Another useful configuration option is `arith := true` which enables arithmetical simplifications. It is so useful
that `simp_arith` is a shorthand for `simp (config := { arith := true })`.
-->

另一个有用的配置是`arith := true`，它会简化算术表达式。因为这太常用了所以用 `simp_arith` 作为`simp (config := { arith := true })`的缩写。

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith
```

<!--
Split Tactic
------------
-->

拆分
------------

<!--
The ``split`` tactic is useful for breaking nested `if-then-else` and `match` expressions in cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals. Here is an example.
-->

``split`` 策略对于在多情形分支结构中打破嵌套的`if-then-else`和 `match` 表达式很有用。
对于包含 `n` 种情形的 `match` 表达式，`split` 策略最多生成 `n` 个子目标。例子：

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

<!--
We can compress the tactic proof above as follows.
-->

可以压缩成一行：

```lean
# def f (x y z : Nat) : Nat :=
#  match x, y, z with
#  | 5, _, _ => y
#  | _, 5, _ => y
#  | _, _, 5 => y
#  | _, _, _ => 1
example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

<!--
The tactic `split <;> first | contradiction | rfl` first applies the `split` tactic,
and then for each generated goal it tries `contradiction`, and then `rfl` if `contradiction` fails.
Like `simp`, we can apply `split` to a particular hypothesis.
-->

策略`split <;> first | contradiction | rfl`首先应用 `split` 策略，接着对每个生成出的目标尝试 `contradiction`，如果失败那么最后 `rfl`。

类似 `simp`，我们对一个特定的假设也可以使用 `split`。

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h
```

<!--
Extensible Tactics
-----------------
-->

扩展策略
-----------------

<!--
In the following example, we define the notation `triv` using the command `syntax`.
Then, we use the command `macro_rules` to specify what should
be done when `triv` is used. You can provide different expansions, and the tactic
interpreter will try all of them until one succeeds.
-->

在下面的例子中，我们使用 `syntax` 命令定义符号 `triv`。然后，我们使用 `macro_rules` 命令来指定使用 `triv` 时应该做什么。你可以提供不同的扩展，策略解释器将尝试所有的扩展，直到有一个成功。

<!--
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
-->

```lean
-- 定义一个新策略符号
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- 你不能用 `triv` 解决下面的定理：
-- example (x : α) : x = x := by
--  triv

-- 扩展 `triv`。策略解释器会尝试所有可能的扩展宏，直到有一个成功。
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- 加一个递归扩展
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```

<!--
Exercises
---------
-->

练习
---------

<!--
1. Go back to the exercises in [Chapter Propositions and
Proofs](./propositions_and_proofs.md) and
[Chapter Quantifiers and Equality](./quantifiers_and_equality.md) and
redo as many as you can now with tactic proofs, using also ``rw``
and ``simp`` as appropriate.

1. Use tactic combinators to obtain a one line proof of the following:
-->

1. 用策略式证明重做[命题与证明](./propositions_and_proofs.md)和[量词与等价](./quantifiers_and_equality.md)两章的练习。适当使用 ``rw`` 和 ``simp``。

2. 用策略组合器给下面的例子用一行写一个证明：
```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit
```
