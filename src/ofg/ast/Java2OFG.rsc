module ofg::ast::Java2OFG

import Set;
import List;
import ofg::ast::FlowLanguage;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;

Program createOFG(loc project) {
	asts = createAstsFromEclipseProject(project, true);
	decls = getDeclarations(asts);
	stms = getStatements(asts);
	return program(decls, stms);
}

set[str] primitiveTypes = {
	"Byte" ,"java.lang.Byte"
	,"Character" ,"java.lang.Character"
	,"Short" ,"java.lang.Short"
	,"Integer" ,"java.lang.Integer"
	,"Long" ,"java.lang.Long"
	,"Float" ,"java.lang.Float"
	,"Double" ,"java.lang.Double"
};
bool ignoreType(arrayType(t)) = ignoreType(t);
bool ignoreType(upperbound(t)) = ignoreType(t);
bool ignoreType(lowerbound(t)) = ignoreType(t);
bool ignoreType(parameterizedType(_)) = false;
bool ignoreType(Type::qualifier(_)) = false;
bool ignoreType(simpleType(t)) = t in primitiveTypes;
bool ignoreType(unionType(tt)) = (false | it || ignoreType(t) | t <- tt);
default bool ignoreType(Type t) = true;


bool ignoreType(TypeSymbol::interface(_,_)) = false;
bool ignoreType(TypeSymbol::\enum(_,_)) = false;
bool ignoreType(TypeSymbol::\typeParameter(_,_)) = false;
bool ignoreType(TypeSymbol::\wildcard(_)) = false;
bool ignoreType(TypeSymbol::\capture(_,_)) = false;
bool ignoreType(TypeSymbol::intersection(tt)) = (false | it || ignoreType(t) | t <- tt);
bool ignoreType(TypeSymbol::union(tt)) = (false | it || ignoreType(t) | t <- tt);
bool ignoreType(TypeSymbol::\class(t,_)) = t == |java+class:///java/lang/String|;
bool ignoreType(TypeSymbol::\object()) = false;
bool ignoreType(TypeSymbol::\array(t,_)) = ignoreType(t);
default bool ignoreType(TypeSymbol t) = true;


set[Decl] getDeclarations(set[Declaration] asts) 
	= { Decl::attribute(v@decl) | /field(t,frags) <- asts, !ignoreType(t), v <- frags}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params, !ignoreType(t)]) | /m:Declaration::method(_,_, params, _, _)  <- asts}
	+ { Decl::method(m@decl, [p@decl | p:parameter(t,_,_) <- params, !ignoreType(t)]) | /m:Declaration::method(_,_, params, _)  <- asts}
	+ { Decl::constructor(c@decl, [p@decl | p:parameter(t,_,_) <- params, !ignoreType(t)]) | /c:Declaration::method(_, params, _,_)  <- asts}      
	// add implicit constructor
	+ { Decl::constructor((c@decl)[scheme="java+constructor"] + "<name>()", []) | /c:class(name, _, _, b) <- asts, !(Declaration::method(_, _, _, _) <- b)}   
	;

set[Stm] getStatements(set[Declaration] asts) {
	allMethods 
		= { m | /m:Declaration::method(_,_,_,_,_) <- asts}
		+ {Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(Type t,n,p,e) <- asts} 
		+ {Declaration::method(simpleType(n), n, p, e, b)[@decl=m@decl] | /m:Declaration::method(str n,p,e, b) <- asts} 
	;
	// now remove all nested classes to make all statements relative to a method
	allMethods = visit(allMethods) {
		case declarationExpression(Declaration::class(_)) => null()
		case declarationExpression(Declaration::class(_,_,_,_)) => null()
		case declarationExpression(Declaration::enum(_,_,_,_)) => null()
		case declarationStatement(Declaration::class(_)) => empty()
		case declarationStatement(Declaration::class(_,_,_,_)) => empty()
		case declarationStatement(Declaration::enum(_,_,_,_)) => empty()
	};
	
	set[Stm] result = {};
	
	for (m:Declaration::method(_, _, _, _, b) <- allMethods) {
		top-down-break visit(b) {
			case \return(e) : 
				result += { *translate(m@decl, m@decl + "return", e)};
			case Expression::assignment(l,_,r) : 
				result += { *translate(m@decl, l@decl, r)};
			case v:Expression::variable(_,_,r) : 
				result += { *translate(m@decl, v@decl, r)};
			// regular method calls with no target
			case m2:Expression::methodCall(_ ,_, _):
				result += { *translate(m@decl, emptyId, m2)};
			case m2:Expression::methodCall(_ ,_, _, _):
				result += { *translate(m@decl, emptyId, m2)};
		}
	}
	return result;
}

// TODO: handle a.b.c => B.c

set[Stm] translate(Id base, Id target, c:cast(_, e)) {
	result = translate(base, target, e);
	return { s.target == target ? s[cast=c@typ.decl] : s | s <- result};
}

set[Stm] translate(Id base, Id target, conditional(con, t, e)) 
	= translate(base, emptyId, con)
	+ translate(base, target, t)
	+ translate(base, target, e)
	;
	
// TODO: check what the second argument could mean (Expr)
set[Stm] translate(Id base, Id target, f:fieldAccess(_,_,_))
	= {Stm::assign(target, emptyId, f@decl)};
set[Stm] translate(Id base, Id target, f:fieldAccess(_,_))
	= {Stm::assign(target, emptyId, f@decl)};

set[Stm] translate(Id base, Id target, s:simpleName(_))
	= {Stm::assign(target, emptyId, s@decl)};

set[Stm] translate(Id base, Id target, m:methodCall(s, n, a))
	= translate(base, target, methodCall(s, this(), n, a)[@decl=m@decl][@typ=m@typ][@src=m@src]);
set[Stm] translate(Id base, Id target, m:methodCall(_, r, n, a)) {
	set[Stm] stms = {};
	Id recv = emptyId;
	if (this() := r) {
		recv = base+"this";	
	}
	else {
		<newId, newStms> = unnestExpressions(base, r@src.offset, [r]);
		assert size(newId) == 1;
		recv = getOneFrom(newId);
		stms += newStms;
	}
	<args, newStms> = unnestExpressions(base, m@src.offset, a);
	return newStms + { Stm::call(target, emptyId, recv, m@decl, args) };
}

set[Stm] translate(Id base, Id target, ob:newObject(_, t, a))
	= translate(base, target, newObject(t, a)[@decl = ob@decl][@typ = ob@typ]);
set[Stm] translate(Id base, Id target, ob:newObject(_, t, a, _))
	= translate(base, target, newObject(t, a)[@decl = ob@decl][@typ = ob@typ]);
set[Stm] translate(Id base, Id target, ob:newObject(t, a,_))
	= translate(base, target, newObject(t, a)[@decl = ob@decl][@typ = ob@typ]);
set[Stm] translate(Id base, Id target, ob:newObject(t, a)) {
	assert target != emptyId;
	if (ignoreType(ob@typ))
		return {};
	
	<args, stms> = unnestExpressions(base, ob@src.offset, a);
	return stms + { Stm::newAssign(target, ob@typ.decl, ob@decl, args)};
}

bool simpleExpression(fieldAccess(_,_,_)) = true;
bool simpleExpression(fieldAccess(_,_)) = true;
bool simpleExpression(cast(_,e)) = simpleExpression(e);
bool simpleExpression(Expression::qualifier(_,e)) = simpleExpression(e);
bool simpleExpression(this()) = true;
bool simpleExpression(this(_)) = true;
bool simpleExpression(simpleName(_)) = true;
bool simpleExpression(arrayAccess(_,_)) = true;
default bool simpleExpression(Expression e) = false;

// for arguments we have to unnestExpressions
//  .. = new A(new B());
// becomes
// __param<unique>_0 = new B();
// .. = new A(__param<unique>_0);
tuple[list[Id], set[Stm]] unnestExpressions(Id prefix, int uniqNum, list[Expression] exprs) {
	list[Id] ids = [];
	set[Stm] newStms = {};
	for (i <- [0..size(exprs)], Expression ce := exprs[i], !ignoreType(ce@typ)) {
		if (simpleExpression(ce)) {
			ids += [ce@decl];	
		}
		else {
			newId = prefix + "__param<uniqNum>_<i>";
			ids += [newId];
			newStms += translate(prefix, newId, ce);
		}
	}
	return <ids, newStms>;
}

default set[Stm] translate(Id base, Id target, Expression e) = { *translate(base, target, ch) | Expression ch <- e};

