{# Copyright (c) The Diem Core Contributors
   SPDX-License-Identifier: Apache-2.0
#}

{# Vectors
   =======
#}

{% macro vector_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}
{%- if options.native_equality -%}
{# Whole vector has native equality #}
function {:inline} $IsEqual'vec{{S}}'(v1: Vec ({{T}}), v2: Vec ({{T}})): bool {
    v1 == v2
}
{%- else -%}
// Not inlined. It appears faster this way.
function $IsEqual'vec{{S}}'(v1: Vec ({{T}}), v2: Vec ({{T}})): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual{{S}}(ReadVec(v1, i), ReadVec(v2, i)))
}
{%- endif %}

// Not inlined.
function $IsValid'vec{{S}}'(v: Vec ({{T}})): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid{{S}}(ReadVec(v, i)))
}

{# TODO: there is an issue with existential quantifier instantiation if we use the native
   functions here without the $IsValid'u64' tag.
#}
{%- if false and instance.has_native_equality -%}
{# Vector elements have native equality #}
function {:inline} $ContainsVec{{S}}(v: Vec ({{T}}), e: {{T}}): bool {
    ContainsVec(v, e)
}

function {:inline} $IndexOfVec{{S}}(v: Vec ({{T}}), e: {{T}}): int {
    IndexOfVec(v, e)
}
{% else %}
function {:inline} $ContainsVec{{S}}(v: Vec ({{T}}), e: {{T}}): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{S}}(ReadVec(v, i), e))
}

function $IndexOfVec{{S}}(v: Vec ({{T}}), e: {{T}}): int;
axiom (forall v: Vec ({{T}}), e: {{T}}:: {$IndexOfVec{{S}}(v, e)}
    (var i := $IndexOfVec{{S}}(v, e);
     if (!$ContainsVec{{S}}(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{S}}(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual{{S}}(ReadVec(v, j), e))));
{% endif %}

function {:inline} $RangeVec{{S}}(v: Vec ({{T}})): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec{{S}}(): Vec ({{T}}) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_empty{{S}}() returns (v: Vec ({{T}})) {
    v := EmptyVec();
}

function {:inline} $1_Vector_$empty{{S}}(): Vec ({{T}}) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_is_empty{{S}}(v: Vec ({{T}})) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_Vector_push_back{{S}}(m: $Mutation (Vec ({{T}})), val: {{T}}) returns (m': $Mutation (Vec ({{T}}))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_Vector_$push_back{{S}}(v: Vec ({{T}}), val: {{T}}): Vec ({{T}}) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_Vector_pop_back{{S}}(m: $Mutation (Vec ({{T}}))) returns (e: {{T}}, m': $Mutation (Vec ({{T}}))) {
    var v: Vec ({{T}});
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_Vector_append{{S}}(m: $Mutation (Vec ({{T}})), other: Vec ({{T}})) returns (m': $Mutation (Vec ({{T}}))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_Vector_reverse{{S}}(m: $Mutation (Vec ({{T}}))) returns (m': $Mutation (Vec ({{T}}))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_Vector_length{{S}}(v: Vec ({{T}})) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_Vector_$length{{S}}(v: Vec ({{T}})): int {
    LenVec(v)
}

procedure {:inline 1} $1_Vector_borrow{{S}}(v: Vec ({{T}}), i: int) returns (dst: {{T}}) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_Vector_$borrow{{S}}(v: Vec ({{T}}), i: int): {{T}} {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_borrow_mut{{S}}(m: $Mutation (Vec ({{T}})), index: int)
returns (dst: $Mutation ({{T}}), m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_Vector_$borrow_mut{{S}}(v: Vec ({{T}}), i: int): {{T}} {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_destroy_empty{{S}}(v: Vec ({{T}})) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_Vector_swap{{S}}(m: $Mutation (Vec ({{T}})), i: int, j: int) returns (m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_Vector_$swap{{S}}(v: Vec ({{T}}), i: int, j: int): Vec ({{T}}) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_Vector_remove{{S}}(m: $Mutation (Vec ({{T}})), i: int) returns (e: {{T}}, m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_Vector_swap_remove{{S}}(m: $Mutation (Vec ({{T}})), i: int) returns (e: {{T}}, m': $Mutation (Vec ({{T}})))
{
    var len: int;
    var v: Vec ({{T}});

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_Vector_contains{{S}}(v: Vec ({{T}}), e: {{T}}) returns (res: bool)  {
    res := $ContainsVec{{S}}(v, e);
}

procedure {:inline 1}
$1_Vector_index_of{{S}}(v: Vec ({{T}}), e: {{T}}) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec{{S}}(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}
{% endmacro vector_module %}


{# BCS
   ====
#}

{% macro bcs_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}
// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function $1_BCS_serialize{{S}}(v: {{T}}): Vec int;

axiom (forall v1, v2: {{T}} :: {$1_BCS_serialize{{S}}(v1), $1_BCS_serialize{{S}}(v2)}
   $IsEqual{{S}}(v1, v2) <==> $IsEqual'vec'u8''($1_BCS_serialize{{S}}(v1), $1_BCS_serialize{{S}}(v2)));

// This says that serialize returns a non-empty vec<u8>
{% if options.serialize_bound == 0 %}
axiom (forall v: {{T}} :: {$1_BCS_serialize{{S}}(v)}
     ( var r := $1_BCS_serialize{{S}}(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 ));
{% else %}
axiom (forall v: {{T}} :: {$1_BCS_serialize{{S}}(v)}
     ( var r := $1_BCS_serialize{{S}}(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 &&
                            LenVec(r) <= {{options.serialize_bound}} ));
{% endif %}

procedure $1_BCS_to_bytes{{S}}(v: {{T}}) returns (res: Vec int);
ensures res == $1_BCS_serialize{{S}}(v);

function {:inline} $1_BCS_$to_bytes{{S}}(v: {{T}}): Vec int {
    $1_BCS_serialize{{S}}(v)
}

{% if S == "'address'" -%}
// Serialized addresses should have the same length.
const $serialized_address_len: int;
// Serialized addresses should have the same length
axiom (forall v: int :: {$1_BCS_serialize'address'(v)}
     ( var r := $1_BCS_serialize'address'(v); LenVec(r) == $serialized_address_len));
{% endif %}
{% endmacro hash_module %}


{# Event Module
   ============
#}

{% macro event_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}

// Map type specific handle to universal one.
type $1_Event_EventHandle{{S}} = $1_Event_EventHandle;

function {:inline} $IsEqual'$1_Event_EventHandle{{S}}'(a: $1_Event_EventHandle{{S}}, b: $1_Event_EventHandle{{S}}): bool {
    a == b
}

function $IsValid'$1_Event_EventHandle{{S}}'(h: $1_Event_EventHandle{{S}}): bool {
    true
}

// Embed event `{{T}}` into universal $EventRep
function {:constructor} $ToEventRep{{S}}(e: {{T}}): $EventRep;
axiom (forall v1, v2: {{T}} :: {$ToEventRep{{S}}(v1), $ToEventRep{{S}}(v2)}
    $IsEqual{{S}}(v1, v2) <==> $ToEventRep{{S}}(v1) == $ToEventRep{{S}}(v2));

// Creates a new event handle. This ensures each time it is called that a unique new abstract event handler is
// returned.
// TODO: we should check (and abort with the right code) if no generator exists for the signer.
procedure {:inline 1} $1_Event_new_event_handle{{S}}(signer: $signer) returns (res: $1_Event_EventHandle{{S}}) {
    assume $1_Event_EventHandles[res] == false;
    $1_Event_EventHandles := $1_Event_EventHandles[res := true];
}

// This boogie procedure is the model of `emit_event`. This model abstracts away the `counter` behavior, thus not
// mutating (or increasing) `counter`.
procedure {:inline 1} $1_Event_emit_event{{S}}(handle_mut: $Mutation $1_Event_EventHandle{{S}}, msg: {{T}})
returns (res: $Mutation $1_Event_EventHandle{{S}}) {
    var handle: $1_Event_EventHandle{{S}};
    handle := $Dereference(handle_mut);
    $es := $ExtendEventStore{{S}}($es, handle, msg);
    res := handle_mut;
}

procedure {:inline 1} $1_Event_destroy_handle{{S}}(handle: $1_Event_EventHandle{{S}}) {
}

function {:inline} $ExtendEventStore{{S}}(
        es: $EventStore, handle: $1_Event_EventHandle{{S}}, msg: {{T}}): $EventStore {
    (var stream := streams#$EventStore(es)[handle];
    (var stream_new := ExtendMultiset(stream, $ToEventRep{{S}}(msg));
    $EventStore(counter#$EventStore(es)+1, streams#$EventStore(es)[handle := stream_new])))
}

function {:inline} $CondExtendEventStore{{S}}(
        es: $EventStore, handle: $1_Event_EventHandle{{S}}, msg: {{T}}, cond: bool): $EventStore {
    if cond then
        $ExtendEventStore{{S}}(es, handle, msg)
    else
        es
}
{% endmacro event_module %}


{# Reflect
    ====
#}
{% macro reflect_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}

type {:datatype} $1_Reflect_TypeInfo;
function {:constructor} $1_Reflect_TypeInfo($addr: int, $mod_name: Vec (int), $type_name: Vec (int)): $1_Reflect_TypeInfo;
function {:inline} $Update'$1_Reflect_TypeInfo'_addr(s: $1_Reflect_TypeInfo, x: int): $1_Reflect_TypeInfo {
    $1_Reflect_TypeInfo(x, $mod_name#$1_Reflect_TypeInfo(s), $type_name#$1_Reflect_TypeInfo(s))
}
function {:inline} $Update'$1_Reflect_TypeInfo'_mod_name(s: $1_Reflect_TypeInfo, x: Vec (int)): $1_Reflect_TypeInfo {
    $1_Reflect_TypeInfo($addr#$1_Reflect_TypeInfo(s), x, $type_name#$1_Reflect_TypeInfo(s))
}
function {:inline} $Update'$1_Reflect_TypeInfo'_type_name(s: $1_Reflect_TypeInfo, x: Vec (int)): $1_Reflect_TypeInfo {
    $1_Reflect_TypeInfo($addr#$1_Reflect_TypeInfo(s), $mod_name#$1_Reflect_TypeInfo(s), x)
}
function $IsValid'$1_Reflect_TypeInfo'(s: $1_Reflect_TypeInfo): bool {
    $IsValid'address'($addr#$1_Reflect_TypeInfo(s))
      && $IsValid'vec'u8''($mod_name#$1_Reflect_TypeInfo(s))
      && $IsValid'vec'u8''($type_name#$1_Reflect_TypeInfo(s))
}
function {:inline} $IsEqual'$1_Reflect_TypeInfo'(s1: $1_Reflect_TypeInfo, s2: $1_Reflect_TypeInfo): bool {
    $IsEqual'address'($addr#$1_Reflect_TypeInfo(s1), $addr#$1_Reflect_TypeInfo(s2))
    && $IsEqual'vec'u8''($mod_name#$1_Reflect_TypeInfo(s1), $mod_name#$1_Reflect_TypeInfo(s2))
    && $IsEqual'vec'u8''($type_name#$1_Reflect_TypeInfo(s1), $type_name#$1_Reflect_TypeInfo(s2))}

// fun Reflect::type_info [verification] at ./sources/Reflect.move:20:5+90
procedure {:timeLimit 40} $1_Reflect_type_info$verify() returns ($ret0: $1_Reflect_TypeInfo)
{
    // declare local variables
    var $t0: int;
    var $t1: Vec (int);
    var $t2: Vec (int);
    var $t3: $1_Reflect_TypeInfo;
    var $temp_0'$1_Reflect_TypeInfo': $1_Reflect_TypeInfo;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 0x1 at ./sources/Reflect.move:20:56+4
    assume {:print "$at(2,498,502)"} true;
    $t0 := 1;
    assume $IsValid'address'($t0);

    // $t1 := [] at ./sources/Reflect.move:20:72+3
    $t1 := $EmptyVec'u8'();
    assume $IsValid'vec'u8''($t1);

    // $t2 := [] at ./sources/Reflect.move:20:88+3
    $t2 := $EmptyVec'u8'();
    assume $IsValid'vec'u8''($t2);

    // $t3 := pack Reflect::TypeInfo($t0, $t1, $t2) at ./sources/Reflect.move:20:39+54
    $t3 := $1_Reflect_TypeInfo($t0, $t1, $t2);

    // trace_return[0]($t3) at ./sources/Reflect.move:20:39+54
    assume {:print "$track_return(0,0,0):", $t3} $t3 == $t3;

    // label L1 at ./sources/Reflect.move:20:94+1
L1:

    // return $t3 at ./sources/Reflect.move:20:94+1
    $ret0 := $t3;
    return;
}

{% endmacro reflect_module %}
