module ofg::ast::FlowLanguage

data Program = program(set[Decl] decls, set[Stm] statemens);

//alias Id = list[IdElem];
alias Id = loc;
public Id emptyId = |id:///|;
/*
data IdElem 
	= packageName(str name)
	| className(str name)
	| methodName(str name)
	| variableName(str name)
	;
*/

data Decl 
	= attribute(Id id)
	| method(Id id, list[Id] formalParameters)
	| constructor(Id id, list[Id] formalParameters)
	;

data Stm
	= newAssign(Id target, Id class, Id ctor, list[Id] actualParameters)
	| assign(Id target, Id cast, Id source)
	| call(Id target, Id cast, Id receiver, Id method, list[Id] actualParameters)
	;