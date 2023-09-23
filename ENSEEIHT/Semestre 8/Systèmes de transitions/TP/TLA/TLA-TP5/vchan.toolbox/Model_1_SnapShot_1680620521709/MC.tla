---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1680620518659179000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1680620518659180000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1680620518659181000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1680620518659182000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1680620518659183000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1680620518659186000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 17:01:58 CEST 2023 by ahamoir
