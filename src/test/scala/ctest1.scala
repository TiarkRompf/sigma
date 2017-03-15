package analysis

// ~/scala/build/pack/bin/scala -cp 'bin:lib/*:lib/java/runtime/*' 

/*
  Parsing C seems to work. Now need to make sense of it.
  - structured form: eliminate gotos
      first compute cfg, then dominators, then reconstruct while/if?

  - compute recurrences / smt interface ?

*/



import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement
import org.eclipse.cdt.core.dom.ast.IASTDeclaration
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement
import org.eclipse.cdt.core.dom.ast.IASTProblem
import org.eclipse.cdt.core.dom.ast.IASTStatement
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage
import org.eclipse.cdt.core.dom.parser.c.ANSICParserExtensionConfiguration
import org.eclipse.cdt.core.dom.parser.c.ICParserExtensionConfiguration
import org.eclipse.cdt.core.index.IIndexFileLocation
import org.eclipse.cdt.core.model.ILanguage
import org.eclipse.cdt.core.parser.FileContent
import org.eclipse.cdt.core.parser.IParserLogService
import org.eclipse.cdt.core.parser.IScannerInfo
import org.eclipse.cdt.core.parser.ParserFactory
import org.eclipse.cdt.internal.core.parser.IMacroDictionary
import org.eclipse.cdt.internal.core.parser.InternalParserUtil
import org.eclipse.cdt.internal.core.parser.scanner.InternalFileContent
import org.eclipse.cdt.internal.core.parser.scanner.InternalFileContentProvider
import org.eclipse.core.runtime.CoreException

import org.eclipse.cdt.core.dom.ast._
import org.eclipse.cdt.internal.core.dom.parser.c._

import java.io.File
import java.io.FileInputStream
import java.io.FileNotFoundException


//val language: ILanguage = new CLanguage(new ANSICParserExtensionConfiguration()) // C99

class CTest1 extends FileDiffSuite {

val prefix = "test-out/test-c-1"

test("A1") { withOutFileChecked(prefix+"A1") {

val language: ILanguage = GCCLanguage.getDefault() // GNUC

val parserLog: IParserLogService = ParserFactory.createDefaultLogService();

def wrapCode(pFileName: String, pCode: String): FileContent = {
   FileContent.create(pFileName, pCode.toCharArray());
}

def wrapFile(pFileName: String): FileContent = {
  def readFile(name: String): String = try {
    val buf = new Array[Byte](new File(name).length().toInt)
    val fis = new FileInputStream(name)
    fis.read(buf)
    fis.close()
    new String(buf)
  } catch {
    case _: FileNotFoundException => ""
  }
    wrapCode(pFileName, readFile(pFileName));
}

val PARSER_OPTIONS = (
            ILanguage.OPTION_IS_SOURCE_UNIT |     // our code files are always source files, not header files
            ILanguage.OPTION_NO_IMAGE_LOCATIONS) // we don't use IASTName#getImageLocation(), so the parse doesn't need to create them


object StubScannerInfo extends IScannerInfo {
  def getDefinedSymbols(): java.util.Map[String,String] = {
    //val macrosBuilder = com.google.common.collect.ImmutableMap.builder[String,String]()
    //macrosBuilder.build()
    new java.util.HashMap
  }
  def getIncludePaths(): Array[String] = new Array(0)
}


object FileContentProvider extends InternalFileContentProvider {
  def getContentForInclusion(pFilePath: IIndexFileLocation,pAstPath: String): InternalFileContent = 
    InternalParserUtil.createFileContent(pFilePath)
  def getContentForInclusion(pFilePath: String,pMacroDictionary: IMacroDictionary): InternalFileContent = 
    InternalParserUtil.createExternalFileContent(pFilePath,
          InternalParserUtil.SYSTEM_DEFAULT_ENCODING);
}


val parsed = language.getASTTranslationUnit(wrapFile("test-in/cpachecker-example.c"), 
  StubScannerInfo, FileContentProvider, null, PARSER_OPTIONS, parserLog)

def recurse(node: org.eclipse.cdt.core.dom.ast.IASTNode, indent: String = ""): Unit = {
    println(indent + node.getClass.getName.replaceAll("org.eclipse.cdt.internal.core.dom.parser.c.","") + ": " + node.getSyntax)
    for (y <- node.getChildren) recurse(y, indent + "  ")
}



val types = Array(
"t_unspecified", // = 0;
"t_void", // = 1;
"t_char", // = 2;
"t_int", // = 3;
"t_float", // = 4;
"t_double", // = 5;
"t_bool", // = 6;
"t_wchar_t", // = 7;
"t_typeof", // = 8;
"t_decltype", // = 9;
"t_auto", // = 10;
"t_char16_t", // = 11;
"t_char32_t" // = 12;
)
assert(types.length == 13)

/*
// An integer literal e.g. 5
public static final int lk_integer_constant = 0;
// A floating point literal e.g. 6.0
public static final int lk_float_constant = 1;
// A char literal e.g. 'a'
public static final int lk_char_constant = 2;
// A string literal e.g. "a literal"
public static final int lk_string_literal = 3;
// <code>lk_this</code> represents the 'this' keyword for  c++ only.
public static final int lk_this = 4;
// <code>lk_true</code> represents the 'true' keyword.
public static final int lk_true = 5;
// <code>lk_false</code> represents the 'false' keyword.
public static final int lk_false = 6;
*/



val operators1 = Array(
// Prefix increment.
// <code>op_prefixIncr</code> ++exp
"op_prefixIncr", // = 0;
// Prefix decrement.
// <code>op_prefixDecr</code> --exp
"op_prefixDecr", // = 1;
// Operator plus.
// <code>op_plus</code> ==> + exp
"op_plus", // = 2;
// Operator minus.
// <code>op_minux</code> ==> -exp
"op_minus", // = 3;
//  Operator star.
//  <code>op_star</code> ==> *exp
"op_star", // = 4;
// Operator ampersand.
// <code>op_amper</code> ==> &exp
"op_amper", // = 5;
// Operator tilde.
// <code>op_tilde</code> ==> ~exp
"op_tilde", // = 6;
// not.
// <code>op_not</code> ==> ! exp
"op_not", // = 7;
// sizeof.
// <code>op_sizeof</code> ==> sizeof exp  
"op_sizeof", // = 8;
// Postfix increment.
// <code>op_postFixIncr</code> ==> exp++
"op_postFixIncr", // = 9;
// Postfix decrement.
// <code>op_bracketedPrimary</code> ==> exp--
"op_postFixDecr", // = 10;
// A bracketed expression.
// <code>op_bracketedPrimary</code> ==> ( exp )
"op_bracketedPrimary", // = 11;
// for c++, only. <code>op_throw</code> throw exp
"op_throw", // = 12;
// for c++, only. <code>op_typeid</code> = typeid( exp )
"op_typeid", // = 13;
// @deprecated Shall not be used, 'typeof something' is not an expression, it's a declaration specifier.
"op_typeof", // = 14;
// for gnu parsers, only. <code>op_alignOf</code> is used for __alignOf( unaryExpression ) type
// expressions.
"op_alignOf", // = 15;
// For c++, only: 'sizeof...(parameterPack)'
// @since 5.2
"op_sizeofParameterPack" // = 16;
)
assert(operators1.length == 17)




val operators2 = Array("ERROR", // empty
// multiply *
"op_multiply", // = 1;
// divide /
"op_divide", // = 2;
// modulo %
"op_modulo", // = 3;
// plus +
"op_plus", // = 4;
// minus -
"op_minus", // = 5;
// shift left <<
"op_shiftLeft", // = 6;
// shift right >>
"op_shiftRight", // = 7;
// less than <
"op_lessThan", // = 8;
// greater than >
"op_greaterThan", // = 9;
// less than or equals <=
"op_lessEqual", // = 10;
// greater than or equals >=
"op_greaterEqual", // = 11;
// binary and &
"op_binaryAnd", // = 12;
// binary Xor ^
"op_binaryXor", // = 13;
// binary Or |
"op_binaryOr", // = 14;
// logical and &&
"op_logicalAnd", // = 15;
// logical or ||
"op_logicalOr", // = 16;
// assignment =
"op_assign", // = 17;
// multiply assignment *=
"op_multiplyAssign", // = 18;
// divide assignemnt /=
"op_divideAssign", // = 19;
// modulo assignment %=
"op_moduloAssign", // = 20;
// plus assignment +=
"op_plusAssign", // = 21;
// minus assignment -=
"op_minusAssign", // = 22;
// shift left assignment <<=
"op_shiftLeftAssign", // = 23;
// shift right assign >>=
"op_shiftRightAssign", // = 24;
// binary and assign &=
"op_binaryAndAssign", // = 25;
// binary Xor assign ^=
"op_binaryXorAssign", // = 26;
// binary Or assign |=
"op_binaryOrAssign", // = 27;
// equals ==
"op_equals", // = 28;
// not equals !=
"op_notequals", // = 29;
// For c==, only. <code>op_pmdot</code> pointer-to-member field dereference.
"op_pmdot", // = 30;
// For c++, only. <code>op_pmarrow</code> pointer-to-member pointer dereference.
"op_pmarrow", // = 31;
// For g++, only. <code>op_max</code> represents >?
"op_max", // = 32;
// For g++, only. <code>op_min</code> represents <?
"op_min", // = 33;
// For gcc compilers, only. <code>op_ellipses</code> represents ... as used for case ranges.
"op_ellipses" //= 34;
)
assert(operators2.length == 35)



def evalExp(node: IASTNode): String = node match {
    case node: CASTLiteralExpression =>
        val lk = node.getKind
        node.toString
    case node: CASTIdExpression =>
        node.getName.toString
    case node: CASTUnaryExpression =>
        val op = operators1(node.getOperator)
        val arg = evalExp(node.getOperand)
        "("+op+" "+arg+")"
    case node: CASTBinaryExpression =>
        val op = operators2(node.getOperator)
        val arg1 = evalExp(node.getOperand1)
        val arg2 = evalExp(node.getOperand2)
        "("+op+" "+arg1+" "+arg2+")"
    case _ => "(exp "+node+")"
}
def evalLocalDecl(node: IASTDeclaration): Unit = node match {
    case node: CASTSimpleDeclaration =>
        val declarators = node.getDeclarators()
        val declSpecifier = node.getDeclSpecifier.asInstanceOf[CASTSimpleDeclSpecifier]

        print(types(declSpecifier.getType))
        print(" ")
        for (d <- declarators) {
            val d1 = d.asInstanceOf[CASTDeclarator]
            val ptr =  d1.getPointerOperators()
            val init = d1.getInitializer.asInstanceOf[CASTEqualsInitializer].getInitializerClause
            print(d1.getName + " = " + evalExp(init))
        }
        println
    case _ => println("dec "+node)
}
def evalStm(node: IASTStatement): Unit = node match {
    case node: CASTCompoundStatement =>
        println("{")
        for (s <- node.getStatements) evalStm(s)
        println("}")
    case node: CASTDeclarationStatement =>
        val decl = node.getDeclaration
        evalLocalDecl(decl)
    case node: CASTExpressionStatement =>
        val exp = node.getExpression
        println(evalExp(exp))
    case node: CASTWhileStatement =>
        val c = node.getCondition
        val b = node.getBody
        println("while "+evalExp(c))
        evalStm(b)
    case node: CASTIfStatement =>
        val c = node.getConditionExpression
        val a = node.getThenClause
        val b = node.getElseClause
        println("if "+evalExp(c))
        evalStm(a)
        println("else")
        evalStm(b)
    case node: CASTLabelStatement =>
        println(node.getName + ":")
        evalStm(node.getNestedStatement)
    case node: CASTGotoStatement =>
        println("goto "+node.getName)
    case node: CASTReturnStatement =>
        println("return "+evalExp(node.getReturnValue))
    case null => 
        println("{}")
    case _ => println("stm "+node)
}
def evalGlobalDecl(node: IASTDeclaration): Unit = node match {
    case node: CASTFunctionDefinition =>
        evalStm(node.getBody)
}
def evalUnit(node: IASTTranslationUnit): Unit = node match {
    case node: CASTTranslationUnit =>
        val decls = node.getDeclarations
        for (d <- decls) evalGlobalDecl(d)

}
evalUnit(parsed)

}}

}