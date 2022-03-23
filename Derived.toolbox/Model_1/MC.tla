---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitTxns
const_164806069300112000 == 
{ << << "x", 1>>, << "y", 3>> >>,
  << << "x", 7>>, << "y", 1>> >>,
  << << "y", 7 >> >>, 
  << << "x", 0>> >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitData
const_164806069300113000 == 
{ << 1, "z", 1 >>, << 0, "z", 2 >>, << 0, "x", 0 >> }
----

====================================================================================================
\* Modification History
\* Created Wed Mar 23 14:38:13 EDT 2022 by bosch
