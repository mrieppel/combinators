// Tree -> String
// Lambda/Combinator Tree to String
function unparsel(t) {
	if(t.length==2 && isLam(t[0]+'.')) {
		return '('+unparsel(t[0])+'.'+unparsel(t[1])+')';
	}
	if(t.length==2) {
		return '('+unparsel(t[0])+unparsel(t[1])+')';
	}
	if(t.length==1) {
		return t[0];
	}
}

// Tree -> Tree
// Lambda Tree to Combinator Tree
function combify(t) {
	if(t.length==2 && isLam(t[0]+'.')) {
		var v = t[0][0];
		if(t[1].length==1 && t[1][0][0]==v[1]) {
			return ['I'];
		}
		if(t[1].length==1 && t[1][0][0]!=v[1]) {
			return [['K'],[t[1][0].charAt(0)]];
		}
		if(t[1].length==2 && t[1][0].length==1 && t[1][0][0][0]=='|') {
			var i = combify(t[1]);
			return combify([t[0],i]);
		}
		if(t[1].length==2) {
			return [ [ ['S'], combify( [[v], t[1][0]] ) ], combify([[v], t[1][1]])];
		}
	} 
	if(t.length==2) {
		return [combify(t[0]), combify(t[1])];
	}
	if(t.length==1) {
		return t;
	}
}

function testcom2(s) {
	return unparsel(combify2(lambdafy(parse(s))));
}

// Tree -> Tree
// Lambda Tree to Combinator Tree
function combify2(t) {
	if(t.length==2 && isLam(t[0]+'.')) {
		var v = t[0][0];
		if(t[1].length==1 && t[1][0][0]==v[1]) {
			return ['I'];
		}
		if(freevar(t[1],[]).indexOf(v[1])<0) {
			return [['K'],t[1]];
		}
		if(t[1].length==2 && t[1][0].length==1 && t[1][0][0].charAt(0)=='|') {
			var i = combify2(t[1]);
			return combify2([t[0],i]);
		}
		if(t[1].length==2 && freevar(t[1],[]).indexOf(v[1])<0 && t[1][1][0]==v[1]){
			return t[1][1];
		}
		if(t[1].length==2 && freevar(t[1][0],[]).indexOf(v[1])>=0 && freevar(t[1][1],[]).indexOf(v[1])>=0) {
			return [ [ ['S'], combify2([[v], t[1][0]]) ], combify2([[v],t[1][1]]) ];
		}
		if(t[1].length==2 && freevar(t[1][0],[]).indexOf(v[1])<0 && freevar(t[1][1],[]).indexOf(v[1])>=0) {
			return [ [ ['B'], t[1][0] ], combify2([[v],t[1][1]]) ];
		}
		if(t[1].length==2 && freevar(t[1][0],[]).indexOf(v[1])>=0 && freevar(t[1][1],[]).indexOf(v[1])<0) {
			return [ [ ['C'], combify2([[v],t[1][0]]) ], t[1][1] ];
		}
	} 
	if(t.length==2) {
		return [combify2(t[0]), combify2(t[1])];
	}
	if(t.length==1) {
		return t;
	}
}


// Tree -> [char] -> [char]
// Takes Lambda tree and an empty array and returns set of free variables in tree
function freevar(t,f) {
	if(t.length==1) {
		return (f.indexOf(t[0])<0 && isLV(t[0])) ? f.concat(t) : f;
	}
	if(t.length==2 && isLam(t[0]+'.')) {
		return freevar(t[1],f).filter(el => el!=t[0][0][1]);
	}
	if(t.length==2) {
		return freevar(t[0],f).concat(freevar(t[1],f));
	}
	else { 
		return [];
	}
}

function testfv(s) {
	return freevar(lambdafy(parse(s)),[]);
}

// Tree -> Tree
// SOL Formula tree to Lambda tree
function lambdafy(t) {
	if(t[0]=='Q') {
		return [[t[1]],[['|'+t[2]],lambdafy(t[3])]];
	}
	if(t[0]=='U') {
		return [[t[1]],lambdafy(t[2])];
	}
	if(t[0]=='B') {
		return [[[t[2]],lambdafy(t[1])],lambdafy(t[3])];
	}
	if(t[0]=='U') {
		return [[t[1]],lambdafy(t[2])];
	}
	if(t[0]=='0p') {
		return [t[1]];
	}
	if(t[0]=='1p') {
		return [[t[1]],[t[2]]];
	}
	if(t[0]=='2p') {
		return [[[t[1]],[t[2]]],[t[3]]];
	}
	if(t[0]=='=') {
		return [[[t[1]],[t[2]]],[t[3]]];
	}
	else {
		return t;
	}
}


// LAMBDA PARSING
// ==============

/* THE GRAMMAR
V :: UVXYZ uwxy
C :: ABCDEFGHJLMNOPQRT abcdefghijklmnopqrst~v&>=
T :: V | C | (TT) | \v.T
*/

function parsel(s) {
	if(s=='') {return [];}
	var s1 = [];
	var s2 = [];
	
	if(isLT(s) || isLV(s)) {
		return [s];
	}
	if(isPEnc(s) && isLam(s.substring(1))) {
		s1 = parsel(s.substring(4,(s.length - 1)));
		return s1.length ? [[s.substring(1,3)], s1] : [];
	}
	if(isPEnc(s) && (isLT(s[1]) || isLV(s[1]))) {
		s1 = parsel(s.substring(2,s.length-1));
		return s1.length ? [[s[1]], s1] : [];
	}
	if(isPEnc(s) && (isLT(s.charAt(s.length-2)) || isLV(s.charAt(s.length-2)))) {
		s1 = parsel(s.substring(1,s.length-2));
		return s1.length ? [s1,[s[s.length-2]]] : [];
	}
	if(isPEnc(s)) {
		var ex = extract(s);
		return (ex[0].length>0 && ex[1].length>0) ? [parsel(ex[0]),parsel(ex[1])] : [];
	} else {
		return [];
	}
}

// String -> Bool
// Determines if string begins with a lambda abstract of the form '|v.'
function isLam(s) {
	return (s.charAt(0)=='|' && isLV(s.charAt(1)) && s.charAt(2)=='.');
}

function isPEnc(s) {
	return (s.charAt(0)=='(' && s.charAt(s.length-1)==')');
}

function extract(s) {
	if(!(s[1]=='(' && s[s.length-2]==')')) {return [[],[]];}
	var stk = [];
	for(var i=0;i<s.length;i++) {
		if(s[i]=='(') {
			stk.push('(');
		}
		if(s[i]==')' && stk.length>0) {
			stk.pop();
		}
		if(i!=0 && stk.length==1) {
			return [s.substring(1,i+1),s.substring(i+1,(s.length-1))];
		}	
	}
}

// Char -> Bool
// Determines if c is a lambda calculus constant
function isLT(c) {
	return c.length==1 && 'ABDEFGHJLMNOPQRTabcdefghijklmnopqrst~v&>='.indexOf(c) >=0;
}

// Char -> Bool
// Determines if c is a lambda calculus variable
function isLV(c) {
	return c.length==1 && 'UVXYZuwxyz'.indexOf(c) >=0;
}


// SOL PARSING
// ===========

/* THE GRAMMAR
S ::= Q S | U S | '(' S B S ')' | A
Q ::= '(A' V ')' | '(E' V ')'
U ::= '~'
B ::= '&' | 'v' | '>'
A ::= '#' | T=T | P | P T | P T T | P T T T ...
P ::= 'A' | 'B' | 'C' | 'D' | ...
T ::= C | V
C :: = 'a' | 'b' | 'c' | 'd'
V :: = 'w' | 'x' | 'y' | 'z' 
*/

// String -> Tree
// Takes a string and if it's a wff, returns a parse tree of the string, otherwise
// returns an empty array.  The first element of any parse tree is always an identifier
// of the type of wff (Q = quantifier wff, B = binary connective wff, P = predicational
// wff etc.) the second element is the wff that's being parsed, and the rest
// is the actual parsing. E.g. "Ax(~Fx&Gx)" parses to:
// [Q,Ax(~Fx&Gx),A,x,[B,(~Fx&Gx),[U,~Fx,~,[P,Fx,F,x]],&,[P,Gx,G,x]]]

function parse(s) {
	if(s=='') {return [];}
	var s1 = [];
	var s2 = [];
	if(isQ(s)) {
		s1 = parse(s.substring(2));
		return s1.length ? ['Q',s.charAt(0),s.charAt(1),s1] : [];
	}
	if(isU(s[0])) {
		s1 = parse(s.substring(1));
		return s1.length ? ['U',s[0],s1] : [];
	}
	if(s[0] =='(' && s[s.length-1]==')') {
		var a = gSub(s);
		if(a.indexOf(undefined)>=0 || a.indexOf('')>=0) {
			return [];
		} else {
			s1 = parse(a[0]);
			s2 = parse(a[2]);
			if(s1.length && s2.length) {
				return ['B',s1,a[1],s2];
			} else {return [];}
		}
	}
	if(isAt(s)) {
		if(s.length==1) {
			return ['0p',s,s];
		}
		if(s.length==2) {
			return ['1p',s[0],s[1]];
		} 
		if(s.length==3 && s[1]=='=') {
			return ['=',s[1],s[0],s[2]];
		}
		if(s.length==3) {
			return ['2p',s[0],s[1],s[2]];
		} else {return [];} // not parsing n-place predicates for n>2 even though isAt() allows them
	
	} else {return [];}
}

// String -> Bool
// Determines if s is an atomic wff
function isAt(s) {
	if(s.length==1 && s==='#') {return true;}
	if(s.length==3 && isIT(s[0]) && s[1]=='=' && isIT(s[2])) {
		return true;
	}
	if(isPT(s[0])) {
	 	if(s.length==1) {
	 		return true;
	 	} else {
	 		for(var i=1;i<s.length;i++) {
	 			if(!isIT(s[i])) {
	 				return false;
	 			}
	 		}
	 		return true;
	 	}
		
	} else {return false;}
}

// String -> Bool
// Determines if s begins with a quantifier
function isQ(s) {
	var q = ['E','A'];
	if(s.length>2 && q.indexOf(s[0])>=0 && (isIV(s[1]) || isPV(s[1])) && !isB(s[2]) && !(isIT(s[2]) && s[3]!=='=')) {
		return true;
	} else {return false;}
}

// String -> Bool
// Determines if s begins with a unary connective
function isU(s) {
	var u = ['~'];
	for(var i=0;i<u.length;i++) {
		if(s.indexOf(u[i])==0) {return true;}
	}
	return false;
}

// String -> [String]
// takes a string beginning with '(' and ending with ')', and determines if there is a
// binary connective enclosed only by the outermost parentheses.  If so, returns an array
// with the string to the left and the string to the right of the binary connective; 
// otherwise returns an array of three undefined's.
function gSub(s) {
	var stk = [];
	var l = 0;
	for(var i=0;i<s.length;i++) {
		if(s[i]=='(') {
			stk.push('(');
		} else if(s[i]==')' && stk.length>0) {
			stk.pop();
		} else if(stk.length==1 && (l = isB(s.substring(i)))>0) {
			return [s.substring(1,i),s.substring(i,i+l),s.substring(i+l,s.length-1)];
		}	
	}
	return [undefined,undefined,undefined];
}

// String -> Int
// takes a string and determines if it begins with a binary connective.  If so, returns
// the length of the connective, otherwise returns 0.
function isB(s) {
	var bc = ['&','v','>'];
	for(var i=0;i<bc.length;i++) {
		if(s.indexOf(bc[i]) == 0) {
			return bc[i].length;
		}
	}
	return 0;
}

// Char -> Bool
// Determines if c is an individual term
function isIT(c) {
	return c.length==1 && (isIC(c) || isIV(c));
}

// Char -> Bool
// Determines if c is an predicate term
function isPT(c) {
	return c.length==1 && (isPC(c) || isPV(c));
}

// Char -> Bool
// Determines if c is an individual variable.
function isIV(c) {
	return c.length==1 && 'uwxyz'.indexOf(c)>=0;
}

// Char -> Bool
// Determines if c is an individual constant
function isIC(c) {
	return c.length==1 && 'abcdefghijklmnopqrst'.indexOf(c)>=0;
}

// Char -> Bool
// Determines if c is a predicate variable.
function isPV(c) {
	return c.length==1 && 'UVXYZ'.indexOf(c)>=0;
}

// Char -> Bool
// Determines if c is a predicate constant
function isPC(c) {
	return c.length==1 && 'DFGHJLMNOPQRT'.indexOf(c)>=0;
}