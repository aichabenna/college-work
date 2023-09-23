---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680620112300116000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680620112300117000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680620112300118000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680620112300119000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680620112300120000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680620112300123000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 16:55:12 CEST 2023 by ahamoir
