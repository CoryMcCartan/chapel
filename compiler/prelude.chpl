// Chapel Prelude

in system __name "system"; // system module

// builtin types

type symbol __name "symbol";
type function __name "function";
type module __name "module";
type continuation __name "continuation";
type any __name "any";
type vector __name "vector";
type tuple __name "tuple";
type void __name "void" : tuple;
type object __name "object" = { };
type list __name "list";
type ref __name "ref";

type catagory __name "catagory";
type set __name "set" : catagory;

type int8 __name "int8";
type int16 __name "int16";
type int32 __name "int32";
type int64 __name "int64";
type int __name "int" = int32;
type uint8 __name "uint8";
type uint16 __name "uint16";
type uint32 __name "uint32";
type uint64 __name "uint64";
type uint __name "uint" = uint32;
type anyint __name "anyint" = 
  int8 | int16 | int32 | int64 |
  uint8 | uint16 | uint32 | uint64;

type float32 __name "float32";
type float64 __name "float64";
type float80 __name "float80";
type float128 __name "float128";
type float __name "float" = float64;
type anyfloat __name "anyfloat" = 
  float32 | float64 | float80 | float128;

type anynum __name "anynum" = anyint | anyfloat;
type size __name "size" = uint32;
type bool __name "bool" = int;
type enum_element __name "enum_element" = int;

// builtin value

null __name "null" : (); 

// global initialization function

__init__ __name "init" : 0;

//   private internal functions
function __make_tuple(...) __name "make_tuple" { 0 };
function __make_list(...) __name "make_list" { 0 } ;
function __make_vector(...) __name "make_vector" { 0 } ;
function __make_set(...) __name "make_set" { 0 } ;
function __make_continuation(...) __name "make_continuation" { 0 };
function __primitive(...) __name "primitive" { 0 } ;
function __new(...) __name "new" { 0 };
function __index_vector(...) __name "index_vector" { 0 };

//   public internal function
function reply(...) __name "reply" { 0 };

// builtin symbols
#operator __name "operator";
#"*" __name "deref";
#"&" __name "doref";

// overloadable primitive operators
function new(a:any) { __new a; }
function operator(a:any, #".", b:symbol)	{ __primitive a #"." b }
function operator(a:any, #"*.", b:symbol)	{ __primitive a #"." b }
function operator(a:anynum, #"*", b:anynum)	{ __primitive a #"*" b }
function operator(a:anynum, #"/", b:anynum)	{ __primitive a #"/" b }
function operator(a:anynum, #"%", b:anynum)	{ __primitive a #"%" b }
function operator(a:anynum, #"+", b:anynum)	{ __primitive a #"+" b }
function operator(a:anynum, #"-", b:anynum)	{ __primitive a #"-" b }
function operator(a:int, #"<<", b:int)		{ __primitive a #"<<" b }
function operator(a:int, #">>", b:int)		{ __primitive a #">>" b }
function operator(a:anynum, #"<", b:anynum)	{ __primitive a #"<" b }
function operator(a:anynum, #"<=", b:anynum)	{ __primitive a #"<=" b }
function operator(a:anynum, #">", b:anynum)	{ __primitive a #">" b }
function operator(a:anynum, #">=", b:anynum)	{ __primitive a #">=" b }
function operator(a:anynum, #"==", b:anynum)	{ __primitive a #"==" b }
function operator(a:anynum, #"!=", b:anynum)	{ __primitive a #"!=" b }
function operator(a:int, #"&", b:int)		{ __primitive a #"&" b }
function operator(a:int, #"^", b:int)		{ __primitive a #"^" b }
function operator(a:int, #"|", b:int)		{ __primitive a #"|" b }
function operator(a:any, #"&&", b:any)		{ __primitive a #"&&" b }
function operator(a:any, #"||", b:any)		{ __primitive a #"||" b }
function operator(a:ref, #"=", b:any)		{ __primitive a #"=" b; }
function operator(a:ref, #"*=", b:anynum)	{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"*" b)
}
function operator(a:ref, #"/=", b:anynum)	{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"/" b)
}
function operator(a:ref, #"%=", b:anynum)	{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"%" b)
}
function operator(a:ref, #"+=", b:anynum)	{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"+" b)
}
function operator(a:ref, #"-=", b:anynum)	{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"-" b)
}
function operator(a:ref, #"<<=", b:int)		{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"<<" b)
}
function operator(a:ref, #">>=", b:int)		{
  __primitive a #"=" (__primitive (__primitive #"*" a) #">>" b)
}
function operator(a:ref, #"&=", b:int)		{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"&" b)
}
function operator(a:ref, #"|=", b:int)		{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"|" b)
}
function operator(a:ref, #"^=", b:int)		{
  __primitive a #"=" (__primitive (__primitive #"*" a) #"^" b)
}
function operator(a:any, #"->", b:symbol)	{ __primitive (__primitive #"*" a) #"." b }
function operator(a:any, #"->*", b:symbol)	{ __primitive (__primitive #"*" a) #"." b; }
function operator(a:anynum, #"^^", b:anynum)	{ __primitive a #"^^" b }
function operator(#"++", a:ref)			{
   __primitive a #"=" ((__primitive #"*" a) #"+" 1)
}
function operator(#"--", a:ref)			{ 
   __primitive a #"=" ((__primitive #"*" a) #"-" 1)
}
function operator(#"+", a:anynum)		{ __primitive #"+" a }
function operator(#"-", a:anynum)		{ __primitive #"-" a }
function operator(#"~", a:anynum)		{ __primitive #"~" a }
function operator(#"!", a:any)			{ __primitive #"!" a }
function operator(#"*", a:any)			{ __primitive #"*" a }
function operator(#"&", a:any)			{ __primitive #"&" a }
function operator(a:anynum, #"|", b:anynum)	{ __primitive a #"|" b }
function operator(#"(", a:symbol, b:any)	{ __primitive #"(" a b }
function operator(a:ref, #"++")			{ 
   __primitive a #"=" ((__primitive #"*" a) #"+" 1)
}
function operator(a:ref, #"--")			{ 
   __primitive a #"=" ((__primitive #"*" a) #"-" 1)
}

// domains

type sequence __name "sequence";
type domain __name "domain";

class distribution {
  type source_domain : domain;
  type destination_domain : domain;
  var source : source_domain;
  var destination : destination_domain;
  function local(i : sequence) : sequence;
  function offset(i : sequence) : sequence;
}

class cyclic implements distribution {
  var width : int;
}

class domain(rank, distribute, target) : vector {
  const rank : int;
  const index : sequence;
  type target : domain;
  type distribute: distribution;
}

function domain::class(s1 : sequence) {
  var d = new domain;
  d.rank = 1;
  d.index = s1;
  return d;
}

function domain::class(s1 : sequence, s2 : sequence) {
  var d = new domain;
  d.rank = 2;
  d.index = new sequence;
  d.index.first = s1.first * s2.first;
  d.index.last = s1.last * s2.last;
  d.index.step = s1.step * s2.step;
  return d;
}

class sequence {
  const first : tuple;
  const last : tuple;
  const step : tuple;
}

function sequence::class afirst alast astep {
  var s = new sequence;
  s.first = afirst;
  s.last = alast;
  s.step = astep;
  return s;
}

function operator(a:sequence, #"*", b:sequence) {
  new sequence
}

function vector::self s { __index_vector self s }
function domain::self s { new domain }

/*
  David's old iterator and domain examples

// iterators

type iterator(a);
type iteratable = {
  type element_type;
  elements : iterator(element_type);
};


// domains

type domain;
type sequence __name "sequence";
type decomposition;
type arithmetic_domain(rank:symbol, distribute:decomposition, to:domain) : domain;
type opaque_domain(distribute:decomposition, to:domain) : domain;
type index(a:domain);
type subdomain(a:domain) = {
  size : int;
  lbound : int -> int;
  ubound : int -> int;
};

type decomposition : catagory = {
  type source : domain, target : domain;
  locale : index(source) -> index(target);
};

type simple_block_decomposition : decomposition = {
  where source : arithmetic_domain(1), target : arithmetic_domain(1);
  s : source;
  t : target;
  chunk : int;
  mod : int;
};

simple_block_decomposition::local(i): {
  k : i / chunk;
  k : (i - s.lbound(1)) / chunk;
  if (k < mod) 
    k += 1;
  k + t.lbound(1)
};

type map(d: domain, a) : iteratable = {
  elements : iterator(a);
  indexes : iterator(index(d));
  operator: #"[" * index(d) -> a &;
};

operator(a:map, #"[", b:index(map::d)): 0;
*/

