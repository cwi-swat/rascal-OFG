module ofg::ast::Java2OFG

import ofg::ast::FlowLanguage;
import lang::java::jdt::m3::AST;

Program createOFG(loc project, str javaVersion = "1.7") {
	asts = createAstsFromEclipseProject(project, true, javaVersion = javaVersion);
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
bool ignoreType(qualifier(_)) = false;
bool ignoreType(simpleType(t)) = t in primitiveTypes;
bool ignoreType(unionType(tt)) = (false | it || ignoreType(t) | t <- tt);
default bool ignoreType(Type t) = true;


bool ignoreType(\interface(_,_)) = false;
bool ignoreType(\enum(_,_)) = false;
bool ignoreType(\typeParameter(_,_)) = false;
bool ignoreType(\wildcard(_)) = false;
bool ignoreType(\capture(_,_)) = false;
bool ignoreType(intersection(tt)) = (false | it || ignoreType(t) | t <- tt);
bool ignoreType(union(tt)) = (false | it || ignoreType(t) | t <- tt);
bool ignoreType(\class(|java+class:///java/lang/String|,_)) = true;
bool ignoreType(\class(_,_)) = false;
bool ignoreType(\object()) = false;
bool ignoreType(\array(t,_)) = ignoreType(t);
default bool ignoreType(TypeSymbol t) = true;


set[Decl] getDeclarations(set[Declaration] asts) 
	= { Decl::attribute(v@decl) | /field(t,frags) <- ast, !ignoreType(t), v <- frags}
	+ { Decl::method(m@decl, [p@decl | parameter(t,_,_) <- params, !ignoreType(t)]) | /m:Declaration::method(_,_, params, _, _)  <- ast}
	+ { Decl::method(m@decl, [p@decl | parameter(t,_,_) <- params, !ignoreType(t)]) | /m:Declaration::method(_,_, params, _)  <- ast}
	+ { Decl::constructor(c@decl, [p@decl | parameter(t,_,_) <- params, !ignoreType(t)]) | /m:Declaration::method(_, params, _,_)  <- ast}      
	// add implicit constructor
	+ { Decl::constructors((c@decl)[scheme="java+constructor"] + "<name>()", []) | /c:class(name, _, _, b) <- asts, !(Declaration::method(_, _, _, _) <- b)}   
	;

set[Stm] getStatements(set[Declaration] asts) {
	allMethods 
		= { m | /m:Declaration::method(_,_,_,_,_) <- asts}
		+ {Declaration::method(t, n, p, e, empty())[@decl=m@decl] | /m:Declaration::method(t,n,p,e) <- asts} 
		+ {Declaration::method(simpleType(n), n, p, e, b)[@decl=m@decl] | /m:Declaration::method(n,p,e, b) <- asts} 
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
			case Expression::assign(l,_,r) : 
				result += { *translate(m@decl, l@decl, r)};
			// regular method calls with no receiver
			case m:Expression::methodCall(_ ,_, _):
				result += { *translate(m@decl, emptyId, m)};
			case m:Expression::methodCall(_ ,_, _, _):
				result += { *translate(m@decl, emptyId, m)};
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

set[Stm] translate(Id base, Id target, m:methodCall(s, n, a))
	= translate(base, target, methodCall(s, this(), n, a)[@decl=m@decl][@typ=m@typ]);
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
	<args, newStms> = unnestExpressions(base, r@src.offset, a);
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
bool simpleExpression(qualifier(_,e)) = simpleExpression(e);
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
	for (i <- [0..size(exprs)], Expression ce := exprs[i], !ignoreType(ce)) {
		if (simpleExpression(ce)) {
			ids += [ce@decl];	
		}
		else {
			newId = prefix + "__param<unique>_<i>";
			ids += [newId];
			newStms += translate(prefix, newId, ce);
		}
	}
	return <ids, newStms>;
}

default set[Stm] translate(Id base, Id target, Expression e) = { *translate(base, target, ch) | Expression ch <- e};

