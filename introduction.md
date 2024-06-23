<!--
Introduction
-->

简介
============

<!--
Computers and Theorem Proving
-->

计算机和定理证明
----------------

<!--
*Formal verification* involves the use of logical and computational methods to establish claims that are expressed in
precise mathematical terms. These can include ordinary mathematical theorems, as well as claims that pieces of hardware
or software, network protocols, and mechanical and hybrid systems meet their specifications. In practice, there is not a
sharp distinction between verifying a piece of mathematics and verifying the correctness of a system: formal
verification requires describing hardware and software systems in mathematical terms, at which point establishing claims
as to their correctness becomes a form of theorem proving. Conversely, the proof of a mathematical theorem may require a
lengthy computation, in which case verifying the truth of the theorem requires verifying that the computation does what
it is supposed to do.
-->

**形式验证（Formal Verification）** 是指使用逻辑和计算方法来验证用精确的数学术语表达的命题。
这包括普通的数学定理，以及硬件或软件、网络协议、机械和混合系统中的形式命题。
在实践中，验证数学命题和验证系统的正确性之间很类似：形式验证用数学术语描述硬件和软件系统，
在此基础上验证其命题的正确性，这就像定理证明的过程。相反，一个数学定理的证明可能需要冗长的计算，
在这种情况下，验证定理的真实性需要验证计算过程是否出错。

<!--
The gold standard for supporting a mathematical claim is to provide a proof, and twentieth-century developments in logic
show most if not all conventional proof methods can be reduced to a small set of axioms and rules in any of a number of
foundational systems. With this reduction, there are two ways that a computer can help establish a claim: it can help
find a proof in the first place, and it can help verify that a purported proof is correct.
-->

二十世纪的逻辑学发展表明，绝大多数传统证明方法可以化为若干基础系统中的一小套公理和规则。
有了这种简化，计算机能以两种方式帮助建立命题：1）它可以帮助寻找一个证明，
2）可以帮助验证一个所谓的证明是正确的。

<!--
*Automated theorem proving* focuses on the "finding" aspect. Resolution theorem provers, tableau theorem provers, fast
satisfiability solvers, and so on provide means of establishing the validity of formulas in propositional and
first-order logic. Other systems provide search procedures and decision procedures for specific languages and domains,
such as linear or nonlinear expressions over the integers or the real numbers. Architectures like SMT ("satisfiability
modulo theories") combine domain-general search methods with domain-specific procedures. Computer algebra systems and
specialized mathematical software packages provide means of carrying out mathematical computations, establishing
mathematical bounds, or finding mathematical objects. A calculation can be viewed as a proof as well, and these systems,
too, help establish mathematical claims.
-->

**自动定理证明（Automated theorem proving）** 着眼于「寻找」证明。
**归结原理（Resolution）** 定理证明器、**表格法（tableau）** 定理证明器、
**快速可满足性求解器（Fast satisfiability solvers）**
等提供了在命题逻辑和一阶逻辑中验证公式有效性的方法；
还有些系统为特定的语言和问题提供搜索和决策程序，
例如整数或实数上的线性或非线性表达式；
像 **SMT（Satisfiability modulo theories，可满足性模理论）**
这样的架构将通用的搜索方法与特定领域的程序相结合；
计算机代数系统和专门的数学软件包提供了进行数学计算或寻找数学对象的手段，
这些系统中的计算也可以被看作是一种证明，而这些系统也可以帮助建立数学命题。

<!--
Automated reasoning systems strive for power and efficiency, often at the expense of guaranteed soundness. Such systems
can have bugs, and it can be difficult to ensure that the results they deliver are correct. In contrast, *interactive
theorem proving* focuses on the "verification" aspect of theorem proving, requiring that every claim is supported by a
proof in a suitable axiomatic foundation. This sets a very high standard: every rule of inference and every step of a
calculation has to be justified by appealing to prior definitions and theorems, all the way down to basic axioms and
rules. In fact, most such systems provide fully elaborated "proof objects" that can be communicated to other systems and
checked independently. Constructing such proofs typically requires much more input and interaction from users, but it
allows you to obtain deeper and more complex proofs.
-->

自动推理系统努力追求能力和效率，但往往牺牲稳定性。这样的系统可能会有 bug，
而且很难保证它们所提供的结果是正确的。相比之下，**交互式定理证明器（Interactive theorem proving）**
侧重于「验证」证明，要求每个命题都有合适的公理基础的证明来支持。
这就设定了非常高的标准：每一条推理规则和每一步计算都必须通过求助于先前的定义和定理来证明，
一直到基本公理和规则。事实上，大多数这样的系统提供了精心设计的「证明对象」，
可以传给其他系统并独立检查。构建这样的证明通常需要用户更多的输入和交互，
但它可以让你获得更深入、更复杂的证明。

<!--
The *Lean Theorem Prover* aims to bridge the gap between interactive and automated theorem proving, by situating
automated tools and methods in a framework that supports user interaction and the construction of fully specified
axiomatic proofs. The goal is to support both mathematical reasoning and reasoning about complex systems, and to verify
claims in both domains.
-->

**Lean 定理证明器** 旨在融合交互式和自动定理证明，
它将自动化工具和方法置于一个支持用户交互和构建完整公理化证明的框架中。
它的目标是支持数学推理和复杂系统的推理，并验证这两个领域的命题。

<!--
Lean's underlying logic has a computational interpretation, and Lean can be viewed equally well as a programming
language. More to the point, it can be viewed as a system for writing programs with a precise semantics, as well as
reasoning about the functions that the programs compute. Lean also has mechanisms to serve as its own *metaprogramming
language*, which means that you can implement automation and extend the functionality of Lean using Lean itself. These
aspects of Lean are described in the free online book, [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), though computational
aspects of the system will make an appearance here.
-->

Lean 的底层逻辑有一个计算的解释，与此同时 Lean 可以被视为一种编程语言。
更重要的是，它可以被看作是一个编写具有精确语义的程序的系统，
以及对程序所表示的计算功能进行推理。Lean 中也有机制使它能够作为它自己的 **元编程语言**，
这意味着你可以使用 Lean 本身实现自动化和扩展 Lean 的功能。
Lean 的这些方面将在本教程的配套教程
[Lean 4函数式编程](https://www.leanprover.cn/fp-lean-zh/)中进行探讨，本书只介绍计算方面。

<!--
About Lean
-->

关于 Lean
----------

<!--
The *Lean* project was launched by Leonardo de Moura at Microsoft Research Redmond in 2013. It is an ongoing, long-term
effort, and much of the potential for automation will be realized only gradually over time. Lean is released under the
[Apache 2.0 license](LICENSE), a permissive open source license that permits others to use and extend the code and
mathematical libraries freely.
-->

*Lean* 项目由微软 Redmond 研究院的 Leonardo de Moura 在 2013 年发起，这是个长期项目，
自动化方法的潜力会在未来逐步被挖掘。Lean 是在 [Apache 2.0 许可协议](LICENSE) 下发布的，
这是一个允许他人自由使用和扩展代码和数学库的许可性开源许可证。


<!--
To install Lean in your computer consider using the [Quickstart](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md) instructions. The Lean source code, and instructions for building Lean, are available at
[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/).


This tutorial describes the current version of Lean, known as Lean 4.
-->

通常有两种办法来运行Lean。第一个是[网页版本](https://live.lean-lang.org/)：
由 JavaScript 编写，包含标准定义和定理库，编辑器会下载到你的浏览器上运行。
这是个方便快捷的办法。

第二种是本地版本：本地版本远快于网页版本，并且非常灵活。Visual Studio Code
和 Emacs 扩展模块给编写和调试证明提供了有力支撑，因此更适合正式使用。
源代码和安装方法见[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/).

本教程介绍的是 Lean 的当前版本：Lean 4。

<!--
About this Book
-->

关于本书
---------------

<!--
This book is designed to teach you to develop and verify proofs in Lean. Much of the background information you will
need in order to do this is not specific to Lean at all. To start with, you will learn the logical system that Lean is
based on, a version of *dependent type theory* that is powerful enough to prove almost any conventional mathematical
theorem, and expressive enough to do it in a natural way. More specifically, Lean is based on a version of a system
known as the Calculus of Constructions with inductive types. Lean can not only define mathematical objects and express
mathematical assertions in dependent type theory, but it also can be used as a language for writing proofs.
-->


本书的目的是教你在 Lean 中编写和验证证明，并且不太需要针对 Lean 的基础知识。首先，你将学习 Lean 所基于的逻辑系统，它是 **依值类型论（Dependent type theory）** 的一个版本，足以证明几乎所有传统的数学定理，并且有足够的表达能力自然地表示数学定理。更具体地说，Lean 是基于具有归纳类型（Inductive type）的构造演算（Calculus of Construction）系统的类型论版本。Lean 不仅可以定义数学对象和表达依值类型论的数学断言，而且还可以作为一种语言来编写证明。

<!--
Because fully detailed axiomatic proofs are so complicated, the challenge of theorem proving is to have the computer
fill in as many of the details as possible. You will learn various methods to support this in [dependent type
theory](dependent_type_theory.md). For example, term rewriting, and Lean's automated methods for simplifying terms and
expressions automatically. Similarly, methods of *elaboration* and *type inference*, which can be used to support
flexible forms of algebraic reasoning.
-->

由于完全深入细节的公理证明十分复杂，定理证明的难点在于让计算机尽可能多地填补证明细节。
你将通过[依值类型论](dependent_type_theory.md)语言来学习各种方法实现自动证明，例如项重写，
以及 Lean 中的项和表达式的自动简化方法。同样，**繁饰（Elaboration）**
和 **类型推断（Type inference）** 的方法，可以用来支持灵活的代数推理。


<!--
Finally, you will learn about features that are specific to Lean, including the language you use to communicate
with the system, and the mechanisms Lean offers for managing complex theories and data.

Throughout the text you will find examples of Lean code like the one below:
-->

最后，你会学到 Lean 的一些特性，包括与系统交流的语言，和 Lean 提供的对复杂理论和数据的管理机制。

在本书中你会见到类似下面这样的代码：

```lean
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
```

<!--
If you are reading the book inside of [VS Code](https://code.visualstudio.com/), you will see a button that reads "try it!" Pressing the button copies the example to your editor with enough surrounding context to make the code compile correctly. You can type
things into the editor and modify the examples, and Lean will check the results and provide feedback continuously as you
type. We recommend running the examples and experimenting with the code on your own as you work through the chapters
that follow. You can open this book on VS Code by using the command "Lean 4: Open Documentation View".
-->

如果你在 [VS Code](https://code.visualstudio.com/) 中阅读本书，你会看到一个按钮，
上面写着「try it!」按下按钮将示例复制到编辑器中，并带有足够的周围上下文，以使代码正确编译。
您可以在编辑器中输入内容并修改示例，Lean 将在您输入时检查结果并不断提供反馈。
我们建议您在阅读后面的章节时，自己运行示例并试验代码。你可以通过使用
「Lean 4: Open Documentation View」命令在 VS Code 中打开本书。

致谢
---------------

<!--
This tutorial is an open access project maintained on Github. Many people have contributed to the effort, providing
corrections, suggestions, examples, and text. We are grateful to Ulrik Buchholz, Kevin Buzzard, Mario Carneiro, Nathan
Carter, Eduardo Cavazos, Amine Chaieb, Joe Corneli, William DeMeo, Marcus Klaas de Vries, Ben Dyer, Gabriel Ebner,
Anthony Hart, Simon Hudon, Sean Leather, Assia Mahboubi, Gihan Marasingha, Patrick Massot, Christopher John Mazey,
Sebastian Ullrich, Floris van Doorn, Daniel Velleman, Théo Zimmerman, Paul Chisholm, Chris Lovett, and Siddhartha Gadgil for their contributions.  Please see [lean prover](https://github.com/leanprover/) and [lean community](https://github.com/leanprover-community/) for an up to date list
of our amazing contributors.
-->

本教程是一项开放源代码项目，在 Github 上维护。许多人为此做出了贡献，提供了
更正、建议、示例和文本。我们要感谢 Ulrik Buchholz、Kevin Buzzard、Mario Carneiro、
Nathan Carter、Eduardo Cavazos、Amine Chaieb、Joe Corneli、William DeMeo、
Marcus Klaas de Vries、Ben Dyer、Gabriel Ebner、Anthony Hart、Simon Hudon、Sean Leather、
Assia Mahboubi、Gihan Marasingha、Patrick Massot、Christopher John Mazey、
Sebastian Ullrich、Floris van Doorn、Daniel Velleman、Théo Zimmerman、Paul Chisholm、Chris Lovett
以及 Siddhartha Gadgil 对本文做出的贡献。有关我们杰出的贡献者的最新名单，
请参见 [Lean 证明器](https://github.com/leanprover/)和 [Lean 社区](https://github.com/leanprover-community/)。
