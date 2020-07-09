.. _coq:

Translation from Stainless to Coq
=================================

Initially based on a project done by `Bence Czipó
<https://github.com/czipobence>`_, this translation is an early experimental
stage.

The `--coq` option of Stainless replaces the standard verification checker
(which uses Inox) by a translation to Coq. Each function from the `*.scala` file
is translated to a Coq file, and obligations corresponding to assertions,
preconditions, and postconditions are solved using predefined tactics in Coq.

.. _coq-requirements:

Requirements
------------

- Coq 8.11.2
- Coq Equations 1.2.2+8.11

These can be installed using `opam
<https://github.com/ocaml/opam/releases/latest>`_ as explained in the `Equations
README.md <https://github.com/mattam82/Coq-Equations>`_.

.. _coq-option:

Usage of the Coq option
-----------------------

First, clone the `Stainless repository
<https://github.com/epfl-lara/stainless>`_. In the `slc-lib` directory, run
`./configure` and `make`.

Then, assuming the Stainless binary ``stainless-scalac`` is in your path, run:
``stainless-scalac --coq File.scala`` on the file of your choice. As an example,
consider the ``test`` function from the `Arith.scala
<https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/coq/Arith.scala>`_
file:

.. code-block:: scala

  def test(a: BigInt, b: BigInt, c: BigInt): BigInt = {
    require(a > b && c > BigInt(0))
    c + a
  } ensuring( _ > c + b )

Running ``stainless-scalac --coq frontends/benchmarks/coq/Arith.scala``
generates the file ``tmp/test.v`` which contains the following Coq definition.

.. code-block:: coq

  Definition test (a: Z) (b: Z) (c: Z) (contractHyp4: (ifthenelse (Z.gtb a b) bool
          (fun _ => Z.gtb c (0)%Z )
          (fun _ => false ) = true)) : {x___1: Z | (Z.gtb x___1 (Z.add c b) = true)} :=
  Z.add c a.

  Fail Next Obligation.

The ``coqc`` executable in run on the file, and the status is reported by
Stainless. In the translation to Coq, the ``BigInt`` type is encoded as ``Z``.
The precondition (``require``) is encoded as an extra argument ``contractHyp4``,
and the postcondition is encoded as a refinement on the return type of `test`.
Here, the obligation related to the postcondition is solved automatically thanks
to the obligation tactic defined above in the ``tmp/test.v`` file. The statement
``Fail Next Obligation.`` then succeeds because all obligations have been solved
(any command in Coq can be prefixed with ``Fail``, and the resulting command
succeeds when the original command fails).
