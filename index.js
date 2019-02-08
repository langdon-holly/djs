#!/usr/bin/env node

'use strict';

const util = require('util')
, fs = require('fs')

, _ = require('lodash')
, codeGen = require('@babel/generator').default
, bb = require('@babel/types')

, iu
  = { done: value => ({done: true, value})
    , elem: value => ({done: false, value})
    , iter: iterable => iterable[Symbol.iterator]()
    , makeIterable: fn => ({[Symbol.iterator]: fn})
    , iterable: iter => iu.makeIterable(() => iter)}
, ps
  = { iteratorIntoIterator
      : (to, from) =>
        { let res = to.next();
          while (!res.done) res = to.next(from.next());
          return res.value;}};

const inspect = o => util.inspect(o, false, null)
, log
  = (...args) =>
    (console.log(args.map(inspect).join("\n")), args[args.length - 1]);

const
  aheadLooker
  = function*(inner)
    { let elems = [], o = inner.next();
      while (!o.done)
        elems.length || elems.push(yield)
        , o = inner.next(o.value.look ? elems[0] : elems.shift());
      return o.value;}
, look0 = {look: 0}
, look1 = {look: 1}

, row0Col0In
  = function*(inner)
    { let row0 = 0, col0 = -1, o, i, eol;
      o = inner.next();
      while (!o.done)
        eol ? (++row0, col0 = 0) : ++col0
        , eol = o.value === 10 /* LF */ && !o.done
        , i = yield o.value
        , o
          = inner.next
            ({...i, value: {o: i.value, row0, col0}});
      return o.value;}

, indexOut
  = function*(inner)
    { let index = 0, i, o;
      while (true)
      { o = inner.next(i);
        if (o.done) return {...o.value, value: {...o.value.value, index}};
        i = yield ++index, o.value;}}

, linesOut
  = function*(inner)
    { let lastLine = [], lines = [lastLine], i, o;
      while (true)
      { o = inner.next(i);
        if (o.done)
          return (
            {...o.value, value: {...o.value.value, lines: lines}});
        i = yield o.value;
        i.done
        ||
          ( i.value === 10 // LF
          ? (lastLine = [], lines.push(lastLine))
          : lastLine.push(i.value));}}

, eofOut
  = function*(inner)
    { let i, o, eof;
      while (true)
      { o = inner.next(i);
        if (o.done) return {...o.value, value: {...o.value.value, eof}};
        eof = (i = yield o.value).done;}}

, ws = Buffer.from(' \t\n\r')
, delimL = Buffer.from('([{')
, delimR = Buffer.from(')]}')
, parenI = delimR.indexOf(')'.codePointAt(0))
, bracketI = delimR.indexOf(']'.codePointAt(0))
, braceI = delimR.indexOf('}'.codePointAt(0))
, ascii
  = _.mapValues
    ( {lf: '\n', hash: '#', backtick: '`', semicolon: ';', bang: '!'}
    , s => s.codePointAt(0));

function *itGen()
{ const n = o => ({done, value} = o).done
  , e = () => iu.done();
  let value, done, stack = [];

  if (!n(yield look1))
  { // Shebang
    if (value.o === ascii.hash)
    { yield look0;
      if (n(yield look0)) return e();
      if (value.o !== ascii.bang) return e();
      do if (n(yield look0)) return e();
      while (value.o !== ascii.lf);}}

  if (n(yield* iu.iterable(specialParser(true)))) return {done, value};
  return iu.elem({tree: value});}

const
  listSpecials
  = [ "script"

    , "o"
    , "?:"
    , ","
    , "list"
    , "unicode"
    , "+"
    , "-"
    , "!"
    , "_++"
    , "++_"
    , "_--"
    , "--_"
    , "eq"
    , "neq"
    , "<"
    , "<="
    , ">"
    , ">="
    , "*"
    , "/"
    , "%"
    , "instanceof"
    , "="
    , "+="
    , "-="
    , "*="
    , "/="
    , "%="
    , "or"
    , "and"
    , "..."
    , "."
    , "f"
    , "fn"
    , "fun"
    , "super"
    , "import"
    , "this"
    , "new"

    , "block"
    , "if"
    , "throw"
    , "noop"
    , "while"
    , "do-while"
    , "loop"
    , "for-of"
    , "return"
    , "break"
    , "try"
    , "let"
    , "const"

    , "null-char"
    , "line-sep"
    , "paragraph-sep"
    , "backspace"
    , "tab"
    , "lf"
    , "vtab"
    , "form-feed"
    , "cr"]
, flatSpecials = ["s", "str"]
, specialParser
  = function *(top)
    { const n = o => ({value, done} = o).done, e = () => iu.done();
      let value, done, commentLevel = 0, beginOk = !0;

      while (1)
      { if (n(yield look1) || delimR.includes(value.o)) return e();
        else if (wsNums.includes(value.o)) beginOk = !0, n(yield look0);
        else if (!beginOk) return e();
        else if (delimL.includes(value.o))
        { if (!commentLevel) return e();
          const dlIndex = delimL.indexOf(value.o)
          , subI
            = commentLevel
              ? delimitedCParser(dlIndex)
              : [callParser, listParser, specialParser][dlIndex]();

          yield look0;
          if (n(yield* iu.iterable(subI))) return e();
          commentLevel--, beginOk = !1;}
        else if (value.o === ascii.semicolon)
          ++commentLevel, beginOk = !0, n(yield look0);
        else
        { if (n(yield* iu.iterable(nameParser()))) return e();
          if (!commentLevel--) break;
          beginOk = !1;}}

      const t = Buffer.from(value).toString();

      let sub;
      if (listSpecials.includes(t)) sub = subElems;
      else if (
        flatSpecials.includes(t) && !n(yield look0) && wsNums.includes(value.o))
        sub = delimitedParser;
      else return e();

      return (
        n(yield* iu.iterable(sub(top ? -1 : braceI)))
        ? e()
        : iu.elem({t, d: value}));}

, delimitedParser
  = function *(delimI)
    { const n = o => ({value, done} = o).done
      , e = () => iu.done()
      , elems = [];
      let value, done, commentLevel = 0;

      while (!n(yield look0) && !delimR.includes(value.o))
      { if (delimL.includes(value.o))
        { const dlIndex = delimL.indexOf(value.o)
          , subI
            = commentLevel
              ? delimitedCParser(dlIndex)
              : [callParser, listParser, specialParser][dlIndex]();

          if (n(yield* iu.iterable(subI))) return e();
          commentLevel ? commentLevel-- : elems.push({t: 'nested', d: value});}
        else if (value.o === ascii.semicolon) ++commentLevel;
        else
        { if (value.o === ascii.backtick && n(yield look0) || commentLevel)
            return e();
          elems.push({t: 'byte', d: value.o});}}
      if (delimI !== (done ? -1 : delimR.indexOf(value.o))) return e();
      return commentLevel ? e() : iu.elem(elems);}
, delimitedCParser
  = function *(delimI)
    { const n = o => ({value, done} = o).done
      , e = () => iu.done()
      , push = elem => commentLevel ? commentLevel-- : elems.push(elem)
      , elems = [];
      let value, done, commentLevel = 0;

      while (!n(yield look0) && !delimR.includes(value.o))
      { if (delimL.includes(value.o))
        { if (n(yield* iu.iterable(delimitedCParser(delimL.indexOf(value.o)))))
            return e();
          push({t: 'nested', d: value});}
        else if (value.o === ascii.semicolon) ++commentLevel;
        else
        { if (value.o === ascii.backtick && n(yield look0)) return e();
          push({t: 'byte', d: value.o});}}
      if (delimI !== (done ? -1 : delimR.indexOf(value.o))) return e();
      return commentLevel ? e() : iu.elem(elems);}
, wsNums = Buffer.from(' \t\n\r')
, nameParser
  = function *()
    { const n = o => ({value, done} = o).done
      , nameDoom = () => value.o === ascii.semicolon || delimL.includes(value.o)
      , nameDone = () => done || [wsNums, delimR].some(b => b.includes(value.o))
      , e = () => iu.done()
      , name = [];
      let value, done;

      while (1)
      { n(yield look1);
        if (nameDone()) return iu.elem(name);
        if (nameDoom()) return e();
        yield look0;
        if (value.o === ascii.backtick && n(yield look0)) return e();
        name.push(value.o);}}
, subElems
  = function *(delimI)
    { const n = o => ({value, done} = o).done
      , e = () => iu.done()
      , push = child => commentLevel ? commentLevel-- : children.push(child)
      , children = [];
      let value, done, commentLevel = 0, beginOk = !0;

      while (1)
      { if (n(yield look1) || delimR.includes(value.o))
          return (
            yield look0
            , commentLevel || delimI !== (done ? -1 : delimR.indexOf(value.o)))
              ? e()
              : iu.elem(children);

        if (wsNums.includes(value.o)) yield look0, beginOk = !0;
        else if (!beginOk) return e();
        else if (delimL.includes(value.o))
        { const dlIndex = delimL.indexOf(value.o)
          , subI
            = commentLevel
              ? delimitedCParser(dlIndex)
              : [callParser, listParser, specialParser][dlIndex]();

          yield look0;
          if (n(yield* iu.iterable(subI))) return e();
          push(value), beginOk = !1;}
        else if (value.o === ascii.semicolon)
          yield look0, ++commentLevel, beginOk = !0;
        else
        { if (n(yield* iu.iterable(nameParser()))) return e();
          push({t: 'ident', d: value}), beginOk = !1;}}}
, callParser
  = function *()
    { let value;
      return (
        ({value} = yield* iu.iterable(subElems(parenI))).done
        ? iu.done()
        : iu.elem({t: 'call', d: value}));}
, listParser
  = function *()
    { let value;
      return (
        ({value} = yield* iu.iterable(subElems(bracketI))).done
        ? iu.done()
        : iu.elem({t: 'block', d: value}));};

const it = () => eofOut(linesOut(indexOut(row0Col0In(aheadLooker(itGen())))))
, parseIterable = iterable => ps.iteratorIntoIterator(it(), iu.iter(iterable));

const
  strEscBuf
  = ast =>
    { switch(ast.t)
      { case 'null-char': return Buffer.from([0]);
        case 'line-sep': return Buffer.from("\u2028");
        case 'paragraph-sep': return Buffer.from("\u2029");
        case 'backspace': return Buffer.from("\u0008");
        case 'tab': return Buffer.from("\u0009");
        case 'lf': return Buffer.from("\u000A");
        case 'vtab': return Buffer.from("\u000B");
        case 'form-feed': return Buffer.from("\u000C");
        case 'cr': return Buffer.from("\u000D");
        case 'unicode':
        return (
          Buffer.concat
          (ast.d.map(c => Buffer.from([parseInt(Buffer.from(c.d).toString())])))
        );}
      return null;}
, patternToBast
  = ast =>
    { switch(ast.t)
      { case 'o':
        return (
          bb.objectPattern
          ( ast.d.map
            ( ({d: [key, val]}) =>
              ( bb.objectProperty
                (exprToBast(key), patternToBast(val), true, false, [])))));
        case 'list':
        return bb.arrayPattern(ast.d.map(patternToBast));
        case '=':
        return (
          bb.assignmentPattern(patternToBast(ast.d[0]), exprToBast(ast.d[1])));
        case '...':
        return bb.restElement(patternToBast(ast.d[0]));}
      return exprToBast(ast);}
, exprToBast
  = ast =>
    { switch(ast.t)
      { case 'ident':
        { const buf = Buffer.from(ast.d);
          if (ast.d.length)
          { const d0 = ast.d[0];
            if (d0 === 39 /* apostrophe */)
              return bb.stringLiteral(buf.slice(1).toString());
            if (d0 === 46 /* period */ || 48 <= d0 && d0 < 58 /* digits */)
              return bb.numericLiteral(parseFloat(buf));}
            if (buf.equals(Buffer.from("null"))) return bb.nullLiteral();
            if (buf.equals(Buffer.from("true"))) return bb.booleanLiteral(!0);
            if (buf.equals(Buffer.from("false"))) return bb.booleanLiteral(!1);
            if (buf.equals(Buffer.from("super"))) return bb.super();
            if (buf.equals(Buffer.from("import"))) return bb.import();
            if (buf.equals(Buffer.from("this"))) return bb.thisExpression();
          return bb.identifier(buf.toString());}
        case 'call':
        return (
          bb.callExpression
          (exprToBast(ast.d[0]), _.tail(ast.d).map(exprToBast)));
        case '?:':
        return (
          bb.conditionalExpression
          (exprToBast(ast.d[0]), exprToBast(ast.d[1]), exprToBast(ast.d[2])));
        case 'o':
        return (
          bb.objectExpression
          ( ast.d.map
            ( ({d: [key, val]}) =>
              ( bb.objectProperty
                (exprToBast(key), exprToBast(val), true, false, [])))));
        case 'list':
        return bb.arrayExpression(ast.d.map(exprToBast));
        case ',':
        return bb.sequenceExpression(ast.d.map(exprToBast));
        case 's':
        return (
          bb.stringLiteral
          ( Buffer.concat
            ( ast.d.map
              ( o =>
                o.t === 'byte'
                ? Buffer.from([o.d])
                : /* 'nested' */ strEscBuf(o.d)))
            .toString()));
        case 'str':
        { let q = [];
          const qs = [q], es = [];
          for (const elem of ast.d)
            elem.t === 'byte'
            ? q.push(elem.d)
            : /* 'nested' */ (es.push(exprToBast(elem.d)), qs.push(q = []));
          const
            quasis
            = qs.map
              ( q =>
                ( bb.templateElement
                  ({cooked: null, raw: Buffer.from(q).toString()}, false)));
          _.last(quasis).tail = true;
          return bb.templateLiteral(quasis, es);}
        case '+':
        case '-':
        return (
          ast.d.length - 1
          ? _.reduce
            ( ast.d.map(exprToBast)
            , (left, right) => bb.binaryExpression(ast.t, left, right))
          : bb.unaryExpression(ast.t, exprToBast(ast.d[0]), !0));
        case '!':
        return bb.unaryExpression(ast.t, exprToBast(ast.d[0]), true);
        case '_++':
        return bb.updateExpression('++', exprToBast(ast.d[0]), !1);
        case '++_':
        return bb.updateExpression('++', exprToBast(ast.d[0]), !0);
        case '_--':
        return bb.updateExpression('--', exprToBast(ast.d[0]), !1);
        case '--_':
        return bb.updateExpression('--', exprToBast(ast.d[0]), !0);
        case 'eq':
        return (
          bb.binaryExpression('===', exprToBast(ast.d[0]), exprToBast(ast.d[1]))
        );
        case 'neq':
        return (
          bb.binaryExpression('!==', exprToBast(ast.d[0]), exprToBast(ast.d[1]))
        );
        case '<':
        case '<=':
        case '>':
        case '>=':
        case '*':
        case '/':
        case '%':
        case 'instanceof':
        return (
          bb.binaryExpression(ast.t, exprToBast(ast.d[0]), exprToBast(ast.d[1]))
        );
        case '=':
        case '+=':
        case '-=':
        case '*=':
        case '/=':
        case '%=':
        return (
          bb.assignmentExpression
          (ast.t, patternToBast(ast.d[0]), exprToBast(ast.d[1])));
        case 'or':
        return (
          ast.d.map(exprToBast).reduce
          ((left, right) => bb.logicalExpression('||', left, right)));
        case 'and':
        return (
          ast.d.map(exprToBast).reduce
          ((left, right) => bb.logicalExpression('&&', left, right)));
        case '...':
        return bb.spreadElement(exprToBast(ast.d[0]));
        case '.':
        return (
          ast.d.map(exprToBast).reduce
          ( (object, property) =>
            bb.memberExpression(object, property, !0, null)));
        case 'f':
        return (
          bb.arrowFunctionExpression
          ( ast.d[0].d.map(patternToBast)
          , exprToBast(ast.d[1])
          , false));
        case 'fn':
        return (
          bb.arrowFunctionExpression
          ( ast.d[0].d.map(patternToBast)
          , bb.blockStatement(ast.d[1].d.map(stmtToBast), [])
          , false));
        case 'fun':
        return (
          bb.functionExpression
          ( null
          , ast.d[0].d.map(patternToBast)
          , bb.blockStatement(ast.d[1].d.map(stmtToBast), [])
          , false
          , false));
        case 'new':
        return (
          bb.newExpression(exprToBast(ast.d[0]), _.tail(ast.d).map(exprToBast))
        );}
      return null;}
, varDeclarate
  = ({d}) =>
    bb.variableDeclarator
    (patternToBast(d[0]), d.length - 1 ? exprToBast(d[1]) : null)
, stmtToBast = ast => 
{ switch (ast.t)
  { case 'block':
    return bb.blockStatement(ast.d.map(stmtToBast), []);
    case 'noop':
    return bb.emptyStatement();
    case 'if':
    return (
      bb.ifStatement
      ( exprToBast(ast.d[0])
      , stmtToBast(ast.d[1]), ast.d.length - 2 ? stmtToBast(ast.d[2]) : null));
    case 'throw':
    return bb.throwStatement(exprToBast(ast.d[0]));
    case 'while':
    return bb.whileStatement(exprToBast(ast.d[0]), stmtToBast(ast.d[1]));
    case 'loop':
    ast.d.unshift({t: 'ident', d: [...Buffer.from("true")]});
    case 'do-while':
    return bb.doWhileStatement(exprToBast(ast.d[0]), stmtToBast(ast.d[1]));
    case 'for-of':
    return (
      bb.forOfStatement
      ( exprToBast(ast.d[0].d[0])
      , exprToBast(ast.d[0].d[1])
      , stmtToBast(ast.d[1])));
    case 'return':
    return bb.returnStatement(ast.d.length ? exprToBast(ast.d[0]) : null);
    case 'break':
    return bb.breakStatement();
    case 'try':
    return (
      bb.tryStatement
      ( bb.blockStatement(ast.d[0].d.map(stmtToBast), [])
      , bb.catchClause(null, bb.blockStatement(ast.d[1].d.map(stmtToBast), []))
      , bb.blockStatement(ast.d[2].d.map(stmtToBast), [])));
    case 'let':
    case 'const':
    return bb.variableDeclaration(ast.t, ast.d.map(varDeclarate));}
  return bb.expressionStatement(exprToBast(ast));}
, toBast
  = ast =>
    ast.t === 'script'
    ? bb.file(bb.program(ast.d.map(stmtToBast), [], "script", null), [], [])
    : stmtToBast(ast);

module.exports
= babel =>
  ( { parserOverride(code, opts)
      { const {done, value} = parseIterable(Buffer.from(code));
        if (done) throw new Error(inspect(value));
        return toBast(value.tree);}});
