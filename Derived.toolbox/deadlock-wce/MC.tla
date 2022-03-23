---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitData
const_16479577402882000 == 
{ << 1, "z", 1 >>, << 0, "z", 2 >>, << 0, "x", 0 >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitTxns
const_16479577402883000 == 
{ << << "x", 1>>, << "y", 3>> >>,
  << << "y", 7>>, << "x", 1>> >>,
  << << "y", 7 >> >>, 
  << << "x", 0>> >> }
----

\* Constant expression definition @modelExpressionEval
const_expr_16479577402894000 == 
ReadAt(InitData, "z", 0)


----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16479577402894000>>)
----

=============================================================================
\* Modification History
\* Created Tue Mar 22 10:02:20 EDT 2022 by bosch
