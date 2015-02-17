module lang::ofg::ast::FlowLanguage

data Program = program(set[Decl] decls, set[Stm] statements);

public loc emptyId = |id:///|;

data Decl 
	= attribute(loc id)
	| method(loc id, list[loc] formalParameters)
	| constructor(loc id, list[loc] formalParameters)
	;

data Stm
	= newAssign(loc target, loc class, loc ctor, list[loc] actualParameters)
	| assign(loc target, loc cast, loc source)
	| call(loc target, loc cast, loc receiver, loc method, list[loc] actualParameters)
	;
