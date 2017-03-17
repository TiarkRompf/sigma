/*******************************************************************************
 * Copyright (c) 2008, 2009 Institute for Software, HSR Hochschule fuer Technik  
 * Rapperswil, University of applied sciences and others
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Eclipse Public License v1.0 
 * which accompanies this distribution, and is available at 
 * http://www.eclipse.org/legal/epl-v10.html  
 *  
 * Contributors: 
 *    Institute for Software - initial API and implementation
 *    Markus Schorn (Wind River Systems)
 *******************************************************************************/

package analysis;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNamespaceDefinition;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateParameter;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.internal.core.dom.rewrite.ASTLiteralNode;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCastExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTDeleteExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTFieldReference;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNewExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTSimpleTypeConstructorExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.gnu.cpp.IGPPASTBinaryExpression;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.c.ICASTTypedefNameSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCompositeTypeSpecifier.ICPPASTBaseSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.parser.Keywords;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCatchHandler;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTForStatement;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTIfStatement;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTryBlockStatement;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.IASTAmbiguousStatement;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;
//import org.eclipse.cdt.internal.core.dom.rewrite.util.FileContentHelper;
//import org.eclipse.cdt.internal.core.dom.rewrite.util.FileHelper;
import org.eclipse.core.resources.IFile;

import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.c.ICASTPointer;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTPointerToMember;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTReferenceOperator;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.gnu.cpp.IGPPASTPointer;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTCatchHandler;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTConstructorChainInitializer;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTExplicitTemplateInstantiation;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTFunctionWithTryBlock;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTLinkageSpecification;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNamespaceAlias;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTNamespaceDefinition;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateDeclaration;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateParameter;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateSpecialization;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTUsingDeclaration;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTUsingDirective;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTVisibilityLabel;
import org.eclipse.cdt.core.parser.Keywords;
import org.eclipse.cdt.internal.core.dom.parser.ASTQueries;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.c.ICASTArrayDesignator;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignator;
import org.eclipse.cdt.core.dom.ast.c.ICASTFieldDesignator;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTConstructorChainInitializer;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTConstructorInitializer;
import org.eclipse.cdt.core.dom.ast.gnu.c.IGCCASTArrayRangeDesignator;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTConversionName;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTQualifiedName;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateId;
import org.eclipse.cdt.internal.core.dom.parser.cpp.CPPTemplateTypeParameter;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTSimpleTypeTemplateParameter;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplateParameter;
import org.eclipse.cdt.core.dom.ast.cpp.ICPPASTTemplatedTypeTemplateParameter;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTMacroExpansionLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNodeLocation;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.index.IIndexMacro;
import org.eclipse.cdt.core.index.IIndexName;
import org.eclipse.cdt.core.index.IndexFilter;
import org.eclipse.cdt.internal.core.pdom.dom.PDOMMacroReferenceName;
import org.eclipse.core.runtime.CoreException;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.cpp.CPPASTVisitor;
import org.eclipse.cdt.internal.core.dom.rewrite.commenthandler.NodeCommentMap;

class ProblemRuntimeException extends RuntimeException {
	public ProblemRuntimeException(IASTNode node) {
		super(node.toString());
	}
}


/**
 * 
 * This class is responsible for the string concatination and the management of
 * the indentations.
 * 
 * @since 5.0
 * @author Emanuel Graf IFS
 * 
 */
class Scribe {
        
        
        private int indentationLevel = 0;
        private int indentationSize = 4; //HSR tcorbat: could be a tab character too - this is not a very elegant solution
        private StringBuffer buffer = new StringBuffer();
        private boolean isAtLineBeginning = true;
        private String newLine = System.getProperty("line.separator"); //$NON-NLS-1$
        private String givenIndentation = null;

        private boolean noNewLine = false;
        private boolean noSemicolon = false;
        
        public void newLine(){
                if(!noNewLine) {
                        isAtLineBeginning = true;
                        buffer.append(getNewline());
                }
        }
        
        private void indent(){
                if( givenIndentation != null ){
                        buffer.append( givenIndentation );
                }
                printSpaces(indentationLevel * indentationSize);
        }
        
        private void indentIfNewLine(){
                if(isAtLineBeginning){
                        isAtLineBeginning = false;
                        indent();
                }
        }
        
        private String getNewline(){
                return newLine;
        }
        
        public void print(String code){
                indentIfNewLine();
                buffer.append(code);
        }
        
        public void println(String code) {
                print(code);
                newLine();
        }
        
        public void print(String code, String code2) {
                print(code);
                buffer.append(code2);
        }
        
        public void println(String code, String code2) {
                print(code, code2);
                newLine();
        }
        
        public void println(String code , char[] code2) {
                print(code);
                buffer.append(code2);
                newLine();
        }
        
        public void printSpaces(int number){
                indentIfNewLine();
                for(int i = 0; i < number; ++i){
                        printSpace();
                }
        }
        
        public void noSemicolon() {
                noSemicolon = true;
        }
        
        public void printSemicolon(){
                if(!noSemicolon) {
                        indentIfNewLine();
                        buffer.append(';');
                }
                else {
                        noSemicolon = false;
                }
        }
        
        @Override
        public String toString(){
                return buffer.toString();
        }
        
        public void print (char code) {
                indentIfNewLine();
                buffer.append(code);
        }

        public void print(char[] code) {
                indentIfNewLine();
                buffer.append(code);
        }
        
        public void println(char[] code) {
                print(code);
                newLine();
        }
        
        public void printStringSpace(String code){
                print(code);
                printSpace();
        }

        /**
         * Prints a { to the Buffer an increases the Indentationlevel.
         */
        public void printLBrace() {
                print('{');
                ++indentationLevel;
        }

        /**
         * Prints a } to the Buffer an decrease the Indentationlevel.
         */
        public void printRBrace() {
                --indentationLevel;
                print('}');
        }
        
        public void incrementIndentationLevel(){
                ++indentationLevel;
        }
        
        public void decrementIndentationLevel(){
                if(indentationLevel>0) {
                        --indentationLevel;
                }
        }
        
        protected void noNewLines(){
                noNewLine = true;
        }
        
        protected void newLines(){
                noNewLine = false;
        }
        
        public void newLine(int i) {
                while(i > 0) {
                        newLine();
                        --i;
                }
        }

        public void printSpace() {
                buffer.append(' ');             
        }

        public String getGivenIndentation() {
                return givenIndentation;
        }

        public void setGivenIndentation(String givenIndentation) {
                this.givenIndentation = givenIndentation;
        }

        public void cleanCache() {
                buffer = new StringBuffer();    
        }
}



/**
 * 
 * Visits all nodes, prints leading comments and handles macro expansions. The
 * source code generation is delegated to severals <code>NodeWriters</code>.
 * 
 * @see NodeWriter
 * @see MacroExpansionHandler
 * 
 * @author Emanuel Graf IFS
 * 
 */
class ASTWriterVisitor extends CPPASTVisitor {
        
        protected Scribe scribe = new Scribe();
        protected NodeCommentMap commentMap;
        protected ExpressionWriter expWriter;
        protected DeclSpecWriter declSpecWriter;
        protected StatementWriter statementWriter;
        protected DeclaratorWriter declaratorWriter;
        protected DeclarationWriter declarationWriter;
        protected InitializerWriter initializerWriter;
        protected NameWriter nameWriter;
        protected TemplateParameterWriter tempParameterWriter;
        protected MacroExpansionHandler macroHandler;
        {
                shouldVisitExpressions = true;
                
                shouldVisitStatements = true;
                
                shouldVisitNames = true;
                
                shouldVisitDeclarations = true;
                
                shouldVisitDeclSpecifiers = true;
                
                shouldVisitDeclarators = true;
                
                shouldVisitArrayModifiers= true;
                
                shouldVisitInitializers = true;
                
                shouldVisitBaseSpecifiers = true;

                shouldVisitNamespaces = true;

                shouldVisitTemplateParameters = true;
                
                shouldVisitParameterDeclarations = true;
                
                shouldVisitTranslationUnit = true;
        }
        
		public ASTWriterVisitor() {
			this(new NodeCommentMap());
		}
        
        public ASTWriterVisitor(NodeCommentMap commentMap) {
                this("", commentMap); //$NON-NLS-1$
        }



        public ASTWriterVisitor(String givenIndentation, NodeCommentMap commentMap) {
                super();
                scribe.setGivenIndentation(givenIndentation);
                init(commentMap);
                this.commentMap = commentMap;

        }

        private void init(NodeCommentMap commentMap) {
                macroHandler = new MacroExpansionHandler(scribe);
                statementWriter = new StatementWriter(scribe,this, commentMap);
                declaratorWriter = new DeclaratorWriter(scribe,this, commentMap);
                declarationWriter = new DeclarationWriter(scribe,this, commentMap);
                declSpecWriter = new DeclSpecWriter(scribe,this, commentMap);
                expWriter = new ExpressionWriter(scribe,this, macroHandler, commentMap);
                initializerWriter = new InitializerWriter (scribe,this, commentMap);
//              ppStmtWriter = new PreprocessorStatementWriter(scribe, this, commentMap);
                nameWriter = new NameWriter(scribe,this, commentMap);
                tempParameterWriter = new TemplateParameterWriter(scribe, this, commentMap);
        }
        
        @Override
        public String toString(){
                return scribe.toString();
        }

        @Override
        public int leave(IASTTranslationUnit tu) {
                for(IASTComment comment : commentMap.getFreestandingCommentsForNode(tu)) {
                        scribe.print(comment.getComment());
                        scribe.newLine();
                }       
                return super.leave(tu);
        }

        private void writeLeadingComments(IASTNode node) {
                for(IASTComment comment : commentMap.getLeadingCommentsForNode(node)) {
                        scribe.print(comment.getComment());
                        scribe.newLine();
                }               
        }
        
        public void visit(ASTLiteralNode lit) {
                scribe.print(lit.getRawSignature());
        }
        
        @Override
        public int visit(IASTName name) {
                writeLeadingComments(name);
                if(!macroHandler.checkisMacroExpansionNode(name)) {
                        nameWriter.writeName(name);
                }
                return ASTVisitor.PROCESS_SKIP;
        }



        @Override
        public int visit(IASTDeclSpecifier declSpec) {
                writeLeadingComments(declSpec);
                declSpecWriter.writeDelcSpec(declSpec);                 
                return ASTVisitor.PROCESS_SKIP;
        }



        @Override
        public int visit(IASTExpression expression) {
                writeLeadingComments(expression);               
                if(!macroHandler.checkisMacroExpansionNode(expression)) {
                        if (expression instanceof IGNUASTCompoundStatementExpression) {
                                IGNUASTCompoundStatementExpression gnuCompStmtExp = (IGNUASTCompoundStatementExpression) expression;
                                gnuCompStmtExp.getCompoundStatement().accept(this);
                        }else {
                                expWriter.writeExpression(expression);
                        }
                }
                return ASTVisitor.PROCESS_SKIP;
        }



        @Override
        public int visit(IASTStatement statement) {
                writeLeadingComments(statement);
                if(macroHandler.isStatementWithMixedLocation(statement) && !(statement instanceof IASTCompoundStatement)){
                        return statementWriter.writeMixedStatement(statement);
                }
                if(macroHandler.checkisMacroExpansionNode(statement)) {
                        return ASTVisitor.PROCESS_SKIP;
                }
                return statementWriter.writeStatement(statement, true);
        }


        @Override
        public int visit(IASTDeclaration declaration) {
                writeLeadingComments(declaration);
                if(!macroHandler.checkisMacroExpansionNode(declaration)) {
                        declarationWriter.writeDeclaration(declaration);
                }
                return  ASTVisitor.PROCESS_SKIP;
        }



        @Override
        public int visit(IASTDeclarator declarator) {
                writeLeadingComments(declarator);
                if(!macroHandler.checkisMacroExpansionNode(declarator)) {
                        declaratorWriter.writeDeclarator(declarator);
                }
                return ASTVisitor.PROCESS_SKIP;
        }

        @Override
        public int visit(IASTArrayModifier amod) {
                if(!macroHandler.checkisMacroExpansionNode(amod)) {
                        declaratorWriter.writeArrayModifier(amod);
                }
                return ASTVisitor.PROCESS_SKIP;
        }


        @Override
        public int visit(IASTInitializer initializer) {
                writeLeadingComments(initializer);
                if(!macroHandler.checkisMacroExpansionNode(initializer)) {
                        initializerWriter.writeInitializer(initializer);
                }
                return ASTVisitor.PROCESS_SKIP;
        }



        @Override
        public int visit(IASTParameterDeclaration parameterDeclaration) {
                writeLeadingComments(parameterDeclaration);
                if(!macroHandler.checkisMacroExpansionNode(parameterDeclaration)) {
                        parameterDeclaration.getDeclSpecifier().accept(this);
                        IASTDeclarator declarator = getParameterDeclarator(parameterDeclaration);
                        
                        if(getParameterName(declarator).toString().length() != 0){
                                scribe.printSpaces(1);
                        }
                        declarator.accept(this);
                }
                return ASTVisitor.PROCESS_SKIP;
        }



        protected IASTName getParameterName(IASTDeclarator declarator) {
                return declarator.getName();
        }


        protected IASTDeclarator getParameterDeclarator(
                        IASTParameterDeclaration parameterDeclaration) {
                return parameterDeclaration.getDeclarator();
        }
        
        @Override
        public int visit(ICPPASTNamespaceDefinition namespace) {
                writeLeadingComments(namespace);
                if(!macroHandler.checkisMacroExpansionNode(namespace)) {
                        declarationWriter.writeDeclaration(namespace);
                }
                return ASTVisitor.PROCESS_SKIP;
        }

        @Override
        public int visit(ICPPASTTemplateParameter parameter) {
                writeLeadingComments(parameter);
                if(!macroHandler.checkisMacroExpansionNode(parameter)) {
                        tempParameterWriter.writeTemplateParameter(parameter);
                }
                return ASTVisitor.PROCESS_SKIP;
        }


        public void cleanCache() {
                scribe.cleanCache();
                macroHandler.reset();
        }

}


/**
 * 
 * Generates source code of expression nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTExpression
 * @author Emanuel Graf IFS
 * 
 */
class ExpressionWriter extends NodeWriter{
        
        private static final String VECTORED_DELETE_OP = "[] "; //$NON-NLS-1$
        private static final String DELETE = "delete "; //$NON-NLS-1$
        private static final String STATIC_CAST_OP = "static_cast<"; //$NON-NLS-1$
        private static final String REINTERPRET_CAST_OP = "reinterpret_cast<"; //$NON-NLS-1$
        private static final String DYNAMIC_CAST_OP = "dynamic_cast<"; //$NON-NLS-1$
        private static final String CONST_CAST_OP = "const_cast<"; //$NON-NLS-1$
        private static final String CLOSING_CAST_BRACKET_OP = ">"; //$NON-NLS-1$
        private static final String ARROW = "->"; //$NON-NLS-1$
        private static final String SPACE_QUESTIONMARK_SPACE = " ? "; //$NON-NLS-1$
        private static final String NEW = "new "; //$NON-NLS-1$
        private static final String CLOSING_BRACKET_OP = ")"; //$NON-NLS-1$
        private static final String TYPEOF_OP = "typeof ("; //$NON-NLS-1$
        private static final String ALIGNOF_OP = "alignof ("; //$NON-NLS-1$
        private static final String TYPEID_OP = "typeid ("; //$NON-NLS-1$
        private static final String OPEN_BRACKET_OP = "("; //$NON-NLS-1$
        private static final String SIZEOF_OP = "sizeof "; //$NON-NLS-1$
        private static final String SIZEOF_PARAMETER_PACK_OP = "sizeof... "; //$NON-NLS-1$
        private static final String NOT_OP = "!"; //$NON-NLS-1$
        private static final String TILDE_OP = "~"; //$NON-NLS-1$
        private static final String AMPERSAND_OP = "&"; //$NON-NLS-1$
        private static final String STAR_OP = "*"; //$NON-NLS-1$
        private static final String UNARY_MINUS_OP = "-"; //$NON-NLS-1$
        private static final String UNARY_PLUS_OP = "+"; //$NON-NLS-1$
        private static final String INCREMENT_OP = "++"; //$NON-NLS-1$
        private static final String DECREMENT_OP = "--"; //$NON-NLS-1$
        private static final String MIN_OP = " <? "; //$NON-NLS-1$
        private static final String MAX_OP = " >? "; //$NON-NLS-1$
        private static final String PMARROW_OP = "->*"; //$NON-NLS-1$
        private static final String PMDOT_OP = ".*"; //$NON-NLS-1$
        private static final String ELLIPSES = " ... "; //$NON-NLS-1$
        private static final String NOT_EQUALS_OP = " != "; //$NON-NLS-1$
        private static final String EQUALS_OP = " == "; //$NON-NLS-1$
        private static final String BINARY_OR_ASSIGN = " |= "; //$NON-NLS-1$
        private static final String BINARY_XOR_ASSIGN_OP = " ^= "; //$NON-NLS-1$
        private static final String BINARY_AND_ASSIGN_OP = " &= "; //$NON-NLS-1$
        private static final String SHIFT_RIGHT_ASSIGN_OP = " >>= "; //$NON-NLS-1$
        private static final String SHIFT_LEFT_ASSIGN_OP = " <<= "; //$NON-NLS-1$
        private static final String MINUS_ASSIGN_OP = " -= "; //$NON-NLS-1$
        private static final String PLUS_ASSIGN_OP = " += "; //$NON-NLS-1$
        private static final String MODULO_ASSIGN_OP = " %= "; //$NON-NLS-1$
        private static final String DIVIDE_ASSIGN_OP = " /= "; //$NON-NLS-1$
        private static final String MULTIPLY_ASSIGN_OP = " *= "; //$NON-NLS-1$
        private static final String LOGICAL_OR_OP = " || "; //$NON-NLS-1$
        private static final String LOGICAL_AND_OP = " && "; //$NON-NLS-1$
        private static final String BINARY_OR_OP = " | "; //$NON-NLS-1$
        private static final String BINARY_XOR_OP = " ^ "; //$NON-NLS-1$
        private static final String BINARY_AND_OP = " & "; //$NON-NLS-1$
        private static final String GREAER_EQUAL_OP = " >= "; //$NON-NLS-1$
        private static final String LESS_EQUAL_OP = " <= "; //$NON-NLS-1$
        private static final String GREATER_THAN_OP = " > "; //$NON-NLS-1$
        private static final String LESS_THAN_OP = " < "; //$NON-NLS-1$
        private static final String SHIFT_RIGHT_OP = " >> "; //$NON-NLS-1$
        private static final String SHIFT_LEFT_OP = " << "; //$NON-NLS-1$
        private static final String MINUS_OP = " - "; //$NON-NLS-1$
        private static final String PLUS_OP = " + "; //$NON-NLS-1$
        private static final String MODULO_OP = " % "; //$NON-NLS-1$
        private static final String DIVIDE_OP = " / "; //$NON-NLS-1$
        private static final String MULTIPLY_OP = " * "; //$NON-NLS-1$
        private final MacroExpansionHandler macroHandler;
        
        public ExpressionWriter(Scribe scribe, CPPASTVisitor visitor, MacroExpansionHandler macroHandler, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
                this.macroHandler = macroHandler;
        }
        
        protected void writeExpression(IASTExpression expression) {
                if (expression instanceof IASTBinaryExpression) {
                        writeBinaryExpression((IASTBinaryExpression) expression);
                } else if (expression instanceof IASTIdExpression) {
                        ((IASTIdExpression) expression).getName().accept(visitor);
                } else if (expression instanceof IASTLiteralExpression) {
                        writeLiteralExpression((IASTLiteralExpression) expression);
                } else if (expression instanceof IASTUnaryExpression) {
                        writeUnaryExpression((IASTUnaryExpression) expression);
                } else if (expression instanceof IASTCastExpression) {
                        writeCastExpression((IASTCastExpression) expression);
                } else if (expression instanceof ICPPASTNewExpression) {
                        writeCPPNewExpression((ICPPASTNewExpression) expression);
                }else if (expression instanceof IASTConditionalExpression) {
                        writeConditionalExpression((IASTConditionalExpression) expression);
                }else if (expression instanceof IASTArraySubscriptExpression) {
                        writeArraySubscriptExpression((IASTArraySubscriptExpression) expression);
                }else if (expression instanceof IASTFieldReference) {
                        writeFieldReference((IASTFieldReference) expression);
                }else if (expression instanceof IASTFunctionCallExpression) {
                        writeFunctionCallExpression((IASTFunctionCallExpression) expression);
                }else if (expression instanceof IASTExpressionList) {
                        writeExpressionList((IASTExpressionList) expression);
                }else if (expression instanceof IASTProblemExpression) {
                        throw new ProblemRuntimeException(((IASTProblemExpression) expression));
                }else if (expression instanceof IASTTypeIdExpression) {
                        writeTypeIdExpression((IASTTypeIdExpression) expression);
                }else if (expression instanceof ICPPASTDeleteExpression) {
                        writeDeleteExpression((ICPPASTDeleteExpression) expression);
                }else if (expression instanceof ICPPASTSimpleTypeConstructorExpression) {
                        writeSimpleTypeConstructorExpression((ICPPASTSimpleTypeConstructorExpression) expression);
                }
        }

        private String getBinaryExpressionOperator(int operator){

                switch(operator){
                case IASTBinaryExpression.op_multiply:
                        return MULTIPLY_OP;
                case IASTBinaryExpression.op_divide:
                        return DIVIDE_OP;
                case IASTBinaryExpression.op_modulo:
                        return MODULO_OP;
                case IASTBinaryExpression.op_plus:
                        return PLUS_OP;
                case IASTBinaryExpression.op_minus:
                        return MINUS_OP;
                case IASTBinaryExpression.op_shiftLeft:
                        return SHIFT_LEFT_OP;
                case IASTBinaryExpression.op_shiftRight:
                        return SHIFT_RIGHT_OP;
                case IASTBinaryExpression.op_lessThan:
                        return LESS_THAN_OP;
                case IASTBinaryExpression.op_greaterThan:
                        return GREATER_THAN_OP;
                case IASTBinaryExpression.op_lessEqual:
                        return LESS_EQUAL_OP;
                case IASTBinaryExpression.op_greaterEqual:
                        return GREAER_EQUAL_OP;
                case IASTBinaryExpression.op_binaryAnd:
                        return BINARY_AND_OP;
                case IASTBinaryExpression.op_binaryXor:
                        return BINARY_XOR_OP;
                case IASTBinaryExpression.op_binaryOr:
                        return BINARY_OR_OP;
                case IASTBinaryExpression.op_logicalAnd:
                        return LOGICAL_AND_OP;
                case IASTBinaryExpression.op_logicalOr:
                        return LOGICAL_OR_OP;
                case IASTBinaryExpression.op_assign:
                        return EQUALS;
                case IASTBinaryExpression.op_multiplyAssign:
                        return MULTIPLY_ASSIGN_OP;
                case IASTBinaryExpression.op_divideAssign:
                        return DIVIDE_ASSIGN_OP;
                case IASTBinaryExpression.op_moduloAssign:
                        return MODULO_ASSIGN_OP;
                case IASTBinaryExpression.op_plusAssign:
                        return PLUS_ASSIGN_OP;
                case IASTBinaryExpression.op_minusAssign:
                        return MINUS_ASSIGN_OP;
                case IASTBinaryExpression.op_shiftLeftAssign:
                        return SHIFT_LEFT_ASSIGN_OP;
                case IASTBinaryExpression.op_shiftRightAssign:
                        return SHIFT_RIGHT_ASSIGN_OP;
                case IASTBinaryExpression.op_binaryAndAssign:
                        return BINARY_AND_ASSIGN_OP;
                case IASTBinaryExpression.op_binaryXorAssign:
                        return BINARY_XOR_ASSIGN_OP;
                case IASTBinaryExpression.op_binaryOrAssign:
                        return BINARY_OR_ASSIGN;
                case IASTBinaryExpression.op_equals:
                        return EQUALS_OP;
                case IASTBinaryExpression.op_notequals:
                        return NOT_EQUALS_OP;
                case ICPPASTBinaryExpression.op_pmdot:
                        return PMDOT_OP;
                case ICPPASTBinaryExpression.op_pmarrow:
                        return PMARROW_OP;
                case IGPPASTBinaryExpression.op_max:
                        return MAX_OP;
                case IGPPASTBinaryExpression.op_min:
                        return MIN_OP;
                case IASTBinaryExpression.op_ellipses:
                        return ELLIPSES;
                default:
                        System.err.println("Unknown unaryExpressionType: " + operator); //$NON-NLS-1$
                        throw new IllegalArgumentException("Unknown unaryExpressionType: " + operator); //$NON-NLS-1$
                }

        }
        
        private boolean isPrefixExpression(IASTUnaryExpression unExp) {
                int unaryExpressionType = unExp.getOperator();

                switch (unaryExpressionType) {
                case IASTUnaryExpression.op_prefixDecr: 
                case IASTUnaryExpression.op_prefixIncr:
                case IASTUnaryExpression.op_plus:
                case IASTUnaryExpression.op_minus:
                case IASTUnaryExpression.op_star:
                case IASTUnaryExpression.op_amper:
                case IASTUnaryExpression.op_tilde:
                case IASTUnaryExpression.op_not:
                case IASTUnaryExpression.op_sizeof:
                case IASTUnaryExpression.op_sizeofParameterPack:
                case IASTUnaryExpression.op_bracketedPrimary:
                case ICPPASTUnaryExpression.op_throw:
                case ICPPASTUnaryExpression.op_typeid:
                case IASTUnaryExpression.op_alignOf: 
                        return true;

                default:
                        return false;
                }
        }
        
        private boolean isPostfixExpression(IASTUnaryExpression unExp) {
                int unaryExpressionType = unExp.getOperator();
                switch (unaryExpressionType) {
                case IASTUnaryExpression.op_postFixDecr:        
                case IASTUnaryExpression.op_postFixIncr:
                case IASTUnaryExpression.op_bracketedPrimary:
                case ICPPASTUnaryExpression.op_typeid:
                case IASTUnaryExpression.op_alignOf:
                        return true;

                default:
                        return false;
                }
        }
        
        private String getPrefixOperator(IASTUnaryExpression unExp) {
                int unaryExpressionType = unExp.getOperator();
                switch (unaryExpressionType) {
                case IASTUnaryExpression.op_prefixDecr: 
                        return DECREMENT_OP;
                case IASTUnaryExpression.op_prefixIncr:
                        return INCREMENT_OP;
                case IASTUnaryExpression.op_plus:
                        return UNARY_PLUS_OP;
                case IASTUnaryExpression.op_minus:
                        return UNARY_MINUS_OP;
                case IASTUnaryExpression.op_star:
                        return STAR_OP;
                case IASTUnaryExpression.op_amper:
                        return AMPERSAND_OP;
                case IASTUnaryExpression.op_tilde:
                        return TILDE_OP;
                case IASTUnaryExpression.op_not:
                        return NOT_OP;
                case IASTUnaryExpression.op_sizeof:
                        return SIZEOF_OP;
                case IASTUnaryExpression.op_sizeofParameterPack:
                        return SIZEOF_PARAMETER_PACK_OP;
                case IASTUnaryExpression.op_bracketedPrimary:
                        return OPEN_BRACKET_OP;
                case ICPPASTUnaryExpression.op_throw:
                        return THROW;
                case ICPPASTUnaryExpression.op_typeid:
                        return TYPEID_OP;
                case IASTUnaryExpression.op_alignOf:
                        return ALIGNOF_OP;
                default:
                        System.err.println("Unkwown unaryExpressionType: " + unaryExpressionType); //$NON-NLS-1$
                throw new IllegalArgumentException("Unkwown unaryExpressionType: " + unaryExpressionType); //$NON-NLS-1$
                }
        }
        
        private String getPostfixOperator(IASTUnaryExpression unExp) {
                int unaryExpressionType = unExp.getOperator();
                switch (unaryExpressionType) {
                case IASTUnaryExpression.op_postFixDecr:
                        return DECREMENT_OP;
                case IASTUnaryExpression.op_postFixIncr:
                        return INCREMENT_OP;
                case ICPPASTUnaryExpression.op_typeid:
                        return CLOSING_BRACKET_OP;
                case IASTUnaryExpression.op_bracketedPrimary:
                case IASTUnaryExpression.op_alignOf:
                        return CLOSING_BRACKET_OP;
                default:
                        System.err.println("Unkwown unaryExpressionType " + unaryExpressionType); //$NON-NLS-1$
                        throw new IllegalArgumentException("Unkwown unaryExpressionType " + unaryExpressionType); //$NON-NLS-1$
                }
        }

        private void writeBinaryExpression(IASTBinaryExpression binExp) {
                IASTExpression operand1 = binExp.getOperand1();
                if (!macroHandler.checkisMacroExpansionNode(operand1)) {
                        operand1.accept(visitor);
                }
                IASTExpression operand2 = binExp.getOperand2();
                if(macroHandler.checkisMacroExpansionNode(operand2, false)&& macroHandler.macroExpansionAlreadyPrinted(operand2)) {
                        return;
                }
                scribe.print(getBinaryExpressionOperator(binExp.getOperator()));
                operand2.accept(visitor);
        }

        private void writeCPPNewExpression(ICPPASTNewExpression newExp) {
                if(newExp.isGlobal()) {
                        scribe.print(COLON_COLON);
                }
                scribe.print(NEW);
                IASTInitializerClause[] placement = newExp.getPlacementArguments();
                if (placement != null) {
                        writeArgumentList(placement);
                }
                                
                IASTTypeId typeId = newExp.getTypeId();
                visitNodeIfNotNull(typeId);
                
                IASTInitializer initExp= getNewInitializer(newExp);
                if (initExp != null) {
                        initExp.accept(visitor);
                }
        }

        protected IASTInitializer getNewInitializer(ICPPASTNewExpression newExp) {
                return newExp.getInitializer();
        }

        private void writeArgumentList(IASTInitializerClause[] args) {
                scribe.print(OPEN_BRACKET_OP);
                boolean needComma= false;
                for (IASTInitializerClause arg : args) {
                        if (needComma) {
                                scribe.print(COMMA_SPACE);
                        }
                        arg.accept(visitor);
                        needComma= true;
                }
                scribe.print(CLOSING_BRACKET_OP);
        }

        private void writeLiteralExpression(IASTLiteralExpression litExp) {
                scribe.print(litExp.toString());
        }

        private void writeUnaryExpression(IASTUnaryExpression unExp) {
                if(isPrefixExpression(unExp )) {
                        scribe.print(getPrefixOperator(unExp));
                }
                visitNodeIfNotNull(unExp.getOperand());
                if(isPostfixExpression(unExp)) {
                        scribe.print(getPostfixOperator(unExp));
                }
        }

        private void writeConditionalExpression(IASTConditionalExpression condExp) {
                condExp.getLogicalConditionExpression().accept(visitor);
                scribe.print(SPACE_QUESTIONMARK_SPACE);
                final IASTExpression positiveExpression = condExp.getPositiveResultExpression();
                // gcc extension allows to omit the positive expression.
                if (positiveExpression == null) {
                        scribe.print(' ');
                }
                else {
                        positiveExpression.accept(visitor);
                }
                scribe.print(SPACE_COLON_SPACE);
                condExp.getNegativeResultExpression().accept(visitor);
                
        }

        private void writeArraySubscriptExpression(IASTArraySubscriptExpression arrSubExp) {
                arrSubExp.getArrayExpression().accept(visitor);
                scribe.print('[');
                arrSubExp.getArgument().accept(visitor);
                scribe.print(']');
                
        }

        private void writeFieldReference(IASTFieldReference fieldRef) {
                fieldRef.getFieldOwner().accept(visitor);
                if(fieldRef.isPointerDereference()) {
                        scribe.print(ARROW);
                }else {
                        scribe.print('.');
                }
                if (fieldRef instanceof ICPPASTFieldReference) {
                        ICPPASTFieldReference cppFieldRef = (ICPPASTFieldReference) fieldRef;
                        if(cppFieldRef.isTemplate()) {
                                scribe.print(TEMPLATE);
                        }
                }
                fieldRef.getFieldName().accept(visitor);
                
        }

        private void writeFunctionCallExpression(IASTFunctionCallExpression funcCallExp) {
                funcCallExp.getFunctionNameExpression().accept(visitor);
                writeArgumentList(funcCallExp.getArguments());
        }

        private void writeCastExpression(IASTCastExpression castExp) {
                scribe.print(getCastPrefix(castExp.getOperator()));
                castExp.getTypeId().accept(visitor);
                scribe.print(getCastPostfix(castExp.getOperator()));
                if (castExp instanceof ICPPASTCastExpression) {
                        scribe.print('(');                      
                }
                castExp.getOperand().accept(visitor);
                if (castExp instanceof ICPPASTCastExpression) {
                        scribe.print(')');                      
                }
        }

        private String getCastPostfix(int castType) {
                switch (castType) {
                case IASTCastExpression.op_cast:
                        return CLOSING_BRACKET_OP;
                case ICPPASTCastExpression.op_const_cast:
                case ICPPASTCastExpression.op_dynamic_cast:
                case ICPPASTCastExpression.op_reinterpret_cast:
                case ICPPASTCastExpression.op_static_cast:
                        return CLOSING_CAST_BRACKET_OP;
                default:
                        throw new IllegalArgumentException("Unknown Cast Type"); //$NON-NLS-1$
                }
        }

        private String getCastPrefix(int castType) {
                switch (castType) {
                case IASTCastExpression.op_cast:
                        return OPEN_BRACKET_OP;
                case ICPPASTCastExpression.op_const_cast:
                        return CONST_CAST_OP;
                case ICPPASTCastExpression.op_dynamic_cast:
                        return DYNAMIC_CAST_OP;
                case ICPPASTCastExpression.op_reinterpret_cast:
                        return REINTERPRET_CAST_OP;
                case ICPPASTCastExpression.op_static_cast:
                        return STATIC_CAST_OP;
                default:
                        throw new IllegalArgumentException("Unknown Cast Type"); //$NON-NLS-1$
                }
        }

        private void writeExpressionList(IASTExpressionList expList) {

                IASTExpression[] expressions = expList.getExpressions();
                writeExpressions(expList, expressions);
        }

        protected void writeExpressions(IASTExpressionList expList, IASTExpression[] expressions) {
                writeNodeList(expressions);
        }

        private void writeTypeIdExpression(IASTTypeIdExpression typeIdExp) {
                scribe.print(getTypeIdExp(typeIdExp));
                typeIdExp.getTypeId().accept(visitor);
                scribe.print(')');              
        }

        private String getTypeIdExp(IASTTypeIdExpression typeIdExp) {
                final int type = typeIdExp.getOperator();
                switch(type) {
                case IASTTypeIdExpression.op_sizeof:
                        return SIZEOF_OP + "("; //$NON-NLS-1$
                case ICPPASTTypeIdExpression.op_typeid:
                        return TYPEID_OP;
                case IGNUASTTypeIdExpression.op_alignof:
                        return ALIGNOF_OP + "("; //$NON-NLS-1$
                case IGNUASTTypeIdExpression.op_typeof:
                        return TYPEOF_OP;
                }
                throw new IllegalArgumentException("Unknown TypeId Type"); //$NON-NLS-1$
        }

        private void writeDeleteExpression(ICPPASTDeleteExpression delExp) {
                if(delExp.isGlobal()) {
                        scribe.print(COLON_COLON);
                }
                scribe.print(DELETE);
                if(delExp.isVectored()) {
                        scribe.print(VECTORED_DELETE_OP);
                }
                delExp.getOperand().accept(visitor);
        }

        private void writeSimpleTypeConstructorExpression(ICPPASTSimpleTypeConstructorExpression simpTypeCtorExp) {
                simpTypeCtorExp.getDeclSpecifier().accept(visitor);
                visitNodeIfNotNull(simpTypeCtorExp.getInitializer());
        }
}




/**
 * 
 * Generates source code of declaration specifier nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTDeclSpecifier
 * @author Emanuel Graf IFS
 * 
 */
class DeclSpecWriter extends NodeWriter {
        private static final String MUTABLE = "mutable "; //$NON-NLS-1$
        private static final String _COMPLEX = "_Complex "; //$NON-NLS-1$
        private static final String LONG_LONG = "long long "; //$NON-NLS-1$
        private static final String REGISTER = "register "; //$NON-NLS-1$
        private static final String AUTO = "auto "; //$NON-NLS-1$
        private static final String TYPEDEF = "typedef "; //$NON-NLS-1$
        private static final String UNION = "union"; //$NON-NLS-1$
        private static final String STRUCT = "struct"; //$NON-NLS-1$
        private static final String CLASS = "class"; //$NON-NLS-1$
        private static final String FRIEND = "friend "; //$NON-NLS-1$
        private static final String EXPLICIT = "explicit "; //$NON-NLS-1$
        private static final String VIRTUAL = "virtual "; //$NON-NLS-1$
        private static final String UNION_SPACE = "union "; //$NON-NLS-1$
        private static final String STRUCT_SPACE = "struct "; //$NON-NLS-1$
        private static final String ENUM = "enum "; //$NON-NLS-1$
        private static final String _BOOL = "_Bool"; //$NON-NLS-1$
        
        public DeclSpecWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
                
        }

        protected void writeDelcSpec(IASTDeclSpecifier declSpec) {
//              Write general DelcSpec Keywords
                writeDeclSpec(declSpec);
                if (declSpec instanceof ICPPASTDeclSpecifier) {
                        writeCPPDeclSpec((ICPPASTDeclSpecifier) declSpec);
                }else if (declSpec instanceof ICASTDeclSpecifier) {
                        writeCDeclSpec((ICASTDeclSpecifier) declSpec);
                }
        }

        private String getCPPSimpleDecSpecifier(ICPPASTSimpleDeclSpecifier simpDeclSpec) {
                return getASTSimpleDecSpecifier(simpDeclSpec.getType(), true);
        }
        
        private String getCSimpleDecSpecifier(ICASTSimpleDeclSpecifier simpDeclSpec) {
                return getASTSimpleDecSpecifier(simpDeclSpec.getType(), false);
        }


        private String getASTSimpleDecSpecifier(int type, boolean isCpp) {

                switch (type) {
                case IASTSimpleDeclSpecifier.t_unspecified:
                        return ""; //$NON-NLS-1$
                case IASTSimpleDeclSpecifier.t_void:
                        return VOID;
                case IASTSimpleDeclSpecifier.t_char:
                        return CHAR;
                case IASTSimpleDeclSpecifier.t_int:
                        return INT;

                case IASTSimpleDeclSpecifier.t_float:
                        return FLOAT;
                case IASTSimpleDeclSpecifier.t_double:
                        return DOUBLE;
                        
                case IASTSimpleDeclSpecifier.t_bool:
                        return isCpp ? CPP_BOOL : _BOOL;
                        
                case IASTSimpleDeclSpecifier.t_wchar_t:
                        if (isCpp)
                                return WCHAR_T;
                        break;
                case IASTSimpleDeclSpecifier.t_char16_t:
                        if (isCpp)
                                return Keywords.CHAR16_T;
                        break;
                case IASTSimpleDeclSpecifier.t_char32_t:
                        if (isCpp)
                                return Keywords.CHAR32_T;
                        break;
                case IASTSimpleDeclSpecifier.t_auto:
                        if (isCpp)
                                return Keywords.AUTO;
                        break;
                case IASTSimpleDeclSpecifier.t_typeof:
                        if (isCpp)
                                return Keywords.TYPEOF;
                        break;
                case IASTSimpleDeclSpecifier.t_decltype:
                        if (isCpp)
                                return Keywords.DECLTYPE;
                        break;
                }

                System.err.println("Unknown specifier type: " + type); //$NON-NLS-1$
                throw new IllegalArgumentException("Unknown specifier type: " + type); //$NON-NLS-1$
        }

        private void writeCDeclSpec(ICASTDeclSpecifier cDeclSpec) {
                if(cDeclSpec.isRestrict()) {
                        scribe.print(RESTRICT);
                }
                
                if (cDeclSpec instanceof ICASTCompositeTypeSpecifier) {
                        writeCompositeTypeSpecifier((ICASTCompositeTypeSpecifier) cDeclSpec);
                }else if (cDeclSpec instanceof ICASTEnumerationSpecifier) {
                        writeEnumSpec((ICASTEnumerationSpecifier) cDeclSpec);
                }else if (cDeclSpec instanceof ICASTElaboratedTypeSpecifier) {
                        writeElaboratedTypeSec((ICASTElaboratedTypeSpecifier) cDeclSpec);
                }else if (cDeclSpec instanceof ICASTSimpleDeclSpecifier) {
                        writeCSimpleDeclSpec((ICASTSimpleDeclSpecifier) cDeclSpec);
                }else if (cDeclSpec instanceof ICASTTypedefNameSpecifier) {
                        writeNamedTypeSpecifier((ICASTTypedefNameSpecifier) cDeclSpec);
                }
        }

        private void writeNamedTypeSpecifier(ICPPASTNamedTypeSpecifier namedSpc) {
                if( namedSpc.isTypename() ){
                        scribe.print(TYPENAME);
                }
                namedSpc.getName().accept(visitor);
        }

        private void writeNamedTypeSpecifier(IASTNamedTypeSpecifier namedSpc) {
                namedSpc.getName().accept(visitor);
        }



        private void writeElaboratedTypeSec(IASTElaboratedTypeSpecifier elabType) {
                scribe.print(getElabTypeString(elabType.getKind()));
                elabType.getName().accept(visitor);
        }



        private String getElabTypeString(int kind) {
                switch(kind) {
                case IASTElaboratedTypeSpecifier.k_enum:
                        return ENUM;
                case IASTElaboratedTypeSpecifier.k_struct:
                        return STRUCT_SPACE;
                case IASTElaboratedTypeSpecifier.k_union:
                        return UNION_SPACE;
                case ICPPASTElaboratedTypeSpecifier.k_class:
                        return CLASS_SPACE;
                        
                default:
                        System.err.println("Unknown ElaboratedType: " + kind); //$NON-NLS-1$
                        throw new IllegalArgumentException("Unknown ElaboratedType: " + kind); //$NON-NLS-1$
                }
        }



        private void writeCPPDeclSpec(ICPPASTDeclSpecifier cppDelcSpec) {
                if (cppDelcSpec.isVirtual()) {
                        scribe.print(VIRTUAL);
                }
                if(cppDelcSpec.isExplicit()) {
                        scribe.print(EXPLICIT);
                }
                if(cppDelcSpec.isFriend()) {
                        scribe.print(FRIEND);
                }
                if(cppDelcSpec.getStorageClass() == IASTDeclSpecifier.sc_mutable) {
                        scribe.print(MUTABLE);
                }
                
                if (cppDelcSpec instanceof ICPPASTCompositeTypeSpecifier) {
                        writeCompositeTypeSpecifier((ICPPASTCompositeTypeSpecifier) cppDelcSpec);
                }else if (cppDelcSpec instanceof IASTEnumerationSpecifier) {
                        writeEnumSpec((IASTEnumerationSpecifier) cppDelcSpec);
                }else if (cppDelcSpec instanceof ICPPASTElaboratedTypeSpecifier) {
                        writeElaboratedTypeSec((ICPPASTElaboratedTypeSpecifier) cppDelcSpec);
                }else if (cppDelcSpec instanceof ICPPASTSimpleDeclSpecifier) {
                        writeCPPSimpleDeclSpec((ICPPASTSimpleDeclSpecifier) cppDelcSpec);
                }else if (cppDelcSpec instanceof ICPPASTNamedTypeSpecifier) {
                        writeNamedTypeSpecifier((ICPPASTNamedTypeSpecifier) cppDelcSpec);
                }
        }



        private void writeEnumSpec(IASTEnumerationSpecifier enumSpec) {
                scribe.print(ENUM);
                enumSpec.getName().accept(visitor);
                scribe.print('{');
                scribe.printSpace();
                IASTEnumerator[] enums = enumSpec.getEnumerators();
                for(int i = 0; i< enums.length;++i) {
                        writeEnumerator(enums[i]);
                        if(i+1< enums.length) {
                                scribe.print(NodeWriter.COMMA_SPACE);
                        }
                }
                scribe.print('}');
                
        }



        private void writeEnumerator(IASTEnumerator enumerator) {
                enumerator.getName().accept(visitor);
                
                IASTExpression value = enumerator.getValue();
                if(value != null) {
                        scribe.print(EQUALS);
                        value.accept(visitor);
                }               
        }



        private void writeCompositeTypeSpecifier(IASTCompositeTypeSpecifier compDeclSpec) {
                boolean hasTrailingComments = hasTrailingComments(compDeclSpec.getName());
                scribe.printStringSpace(getCPPCompositeTypeString(compDeclSpec.getKey()));
                compDeclSpec.getName().accept(visitor);
                if (compDeclSpec instanceof ICPPASTCompositeTypeSpecifier) {
                        ICPPASTCompositeTypeSpecifier cppComp = (ICPPASTCompositeTypeSpecifier) compDeclSpec;
                        ICPPASTBaseSpecifier[] baseSpecifiers = cppComp.getBaseSpecifiers();
                        if (baseSpecifiers.length > 0) {
                                scribe.print(SPACE_COLON_SPACE);
                                for(int i = 0; i < baseSpecifiers.length;++i) {
                                        writeBaseSpecifiers(baseSpecifiers[i]);
                                        if(i+1 < baseSpecifiers.length) {
                                                scribe.print(COMMA_SPACE);
                                        }
                                }
                                hasTrailingComments = hasTrailingComments(baseSpecifiers[baseSpecifiers.length-1].getName());
                        }
                }
                if(!hasTrailingComments){
                        scribe.newLine();
                }
                scribe.print('{');
                scribe.newLine();
                scribe.incrementIndentationLevel();
                IASTDeclaration[] decls = getMembers(compDeclSpec);
                
                if(decls.length > 0) {
                        for (IASTDeclaration declaration : decls) {
                                declaration.accept(visitor);
                        }
                }

                if(hasFreestandingComments(compDeclSpec)) {
                        writeFreeStandingComments(compDeclSpec);                        
                }
                scribe.decrementIndentationLevel();
                scribe.print('}');

                if(hasTrailingComments(compDeclSpec)) {
                        writeTrailingComments(compDeclSpec);                    
                }
        }

        protected IASTDeclaration[] getMembers(IASTCompositeTypeSpecifier compDeclSpec) {
                return compDeclSpec.getMembers();
        }

        private void writeBaseSpecifiers(ICPPASTBaseSpecifier specifier) {
                switch(specifier.getVisibility()) {
                case ICPPASTBaseSpecifier.v_public:
                        scribe.printStringSpace(PUBLIC);
                        break;
                case ICPPASTBaseSpecifier.v_protected:
                        scribe.printStringSpace(PROTECTED);
                        break;
                case ICPPASTBaseSpecifier.v_private:
                        scribe.printStringSpace(PRIVATE);
                        break;
                }
                specifier.getName().accept(visitor);
        }



        private String getCPPCompositeTypeString(int key) {
                if(key <= IASTCompositeTypeSpecifier.k_last) {
                        return getCompositeTypeString(key);
                }
                switch (key) {
                case ICPPASTCompositeTypeSpecifier.k_class:
                        return CLASS;
                default:
                        System.err.println("Unknow Specifiertype: " + key); //$NON-NLS-1$
                        throw new IllegalArgumentException("Unknow Specifiertype: " + key); //$NON-NLS-1$
                }
        }



        private String getCompositeTypeString(int key) {
                switch (key) {
                case IASTCompositeTypeSpecifier.k_struct:
                        return STRUCT;
                case IASTCompositeTypeSpecifier.k_union:
                        return UNION;
                default:
                        System.err.println("Unknow Specifiertype: " + key); //$NON-NLS-1$
                        throw new IllegalArgumentException("Unknow Specifiertype: " + key); //$NON-NLS-1$
                }
        }



        private void writeDeclSpec(IASTDeclSpecifier declSpec) {
                if(declSpec.isInline()) {
                        scribe.print(INLINE);
                }
                switch(declSpec.getStorageClass()) {
                case IASTDeclSpecifier.sc_typedef:
                        scribe.print(TYPEDEF);
                        break;
                case IASTDeclSpecifier.sc_extern:
                        scribe.print(EXTERN);
                        break;
                case IASTDeclSpecifier.sc_static:
                        scribe.print(STATIC);
                        break;
                case IASTDeclSpecifier.sc_auto:
                        scribe.print(AUTO);
                        break;
                case IASTDeclSpecifier.sc_register:
                        scribe.print(REGISTER);
                        break;
                }
                if (declSpec.isConst()) {
                        scribe.printStringSpace(CONST);
                }
                if (declSpec.isVolatile()) {
                        scribe.printStringSpace(VOLATILE);
                }
                
                
        }

        private void writeCPPSimpleDeclSpec(ICPPASTSimpleDeclSpecifier simpDeclSpec) {
                printQualifiers(simpDeclSpec);
                scribe.print(getCPPSimpleDecSpecifier(simpDeclSpec));
                if (simpDeclSpec.getType() == IASTSimpleDeclSpecifier.t_typeof) {
                        scribe.printSpace();
                        visitNodeIfNotNull(simpDeclSpec.getDeclTypeExpression());
                } else if (simpDeclSpec.getType() == IASTSimpleDeclSpecifier.t_decltype) {
                        scribe.print('(');
                        visitNodeIfNotNull(simpDeclSpec.getDeclTypeExpression());
                        scribe.print(')');
                }
        }
        
        private void printQualifiers(IASTSimpleDeclSpecifier simpDeclSpec) {
                if(simpDeclSpec.isSigned()) {
                        scribe.printStringSpace(SIGNED);
                }else if(simpDeclSpec.isUnsigned()){
                        scribe.printStringSpace(UNSIGNED);
                }
                
                if(simpDeclSpec.isShort()) {
                        scribe.printStringSpace(SHORT);
                }else if(simpDeclSpec.isLong()) {
                        scribe.printStringSpace(LONG);
                }else if(simpDeclSpec.isLongLong()) {                   
                        scribe.print(LONG_LONG);
                }
                if (simpDeclSpec instanceof ICASTSimpleDeclSpecifier) {
                        ICASTSimpleDeclSpecifier cSimpDeclSpec = (ICASTSimpleDeclSpecifier) simpDeclSpec;
                        if (cSimpDeclSpec.isComplex()) {
                                scribe.print(_COMPLEX);
                        }
                }
        }



        private void writeCSimpleDeclSpec(ICASTSimpleDeclSpecifier simpDeclSpec) {
                printQualifiers(simpDeclSpec);
                scribe.print(getCSimpleDecSpecifier(simpDeclSpec));
        }

}


/**
 * 
 * Generates source code of statement nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTStatement
 * @author Emanuel Graf IFS
 * 
 */
class StatementWriter extends NodeWriter{

        private static final String DEFAULT = "default:"; //$NON-NLS-1$
        private static final String CASE = "case "; //$NON-NLS-1$
        private static final String WHILE = "while("; //$NON-NLS-1$
        private static final String TRY = "try "; //$NON-NLS-1$
        private static final String CATCH = "catch("; //$NON-NLS-1$
        private static final String RETURN = "return"; //$NON-NLS-1$
        private static final String GOTO = "goto "; //$NON-NLS-1$
        private static final String CONTINUE = "continue"; //$NON-NLS-1$
        private static final String BREAK = "break"; //$NON-NLS-1$
        private static final String ELSE = "else"; //$NON-NLS-1$
        private static final String IF = "if("; //$NON-NLS-1$
        private static final String FOR = "for("; //$NON-NLS-1$
        private static final String DO_WHILE = " while("; //$NON-NLS-1$
        private static final String DO = "do"; //$NON-NLS-1$
        private static final String SWITCH_BRACKET = "switch ("; //$NON-NLS-1$
        private boolean compoundNoNewLine = false;
        private boolean switchIsNew;
        private boolean decrementIndentationLevelOneMore = false;
        private final DeclarationWriter declWriter;

        public StatementWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
                declWriter = new DeclarationWriter(scribe, visitor, commentMap);
        }
        
        /**
         * 
         * @param statement
         * @param newLine if true print a newline if statment usually have one.
         * @return {@link ASTVisitor#PROCESS_SKIP}
         */
        protected int writeStatement(IASTStatement statement, boolean newLine) {
                if (statement instanceof IASTAmbiguousStatement) {
                        //TODO HSR Leo test
                        statement.accept(visitor);
                        newLine = false;
                } else if (statement instanceof IASTExpressionStatement) {
                        writeExpressionStatement((IASTExpressionStatement) statement);
                        //usually newLine
                } else if (statement instanceof IASTDeclarationStatement) {
                        writeDeclarationStatement((IASTDeclarationStatement) statement);
                        newLine = false;
                } else if (statement instanceof IASTNullStatement) {
                        writeNullStatement((IASTNullStatement)statement);
//                      usually newLine
                } else if (statement instanceof IASTReturnStatement) {
                        writeReturnStatement((IASTReturnStatement)statement);
//                      usually newLine
                } else if (statement instanceof IASTGotoStatement) {
                        writeGotoStatement((IASTGotoStatement) statement);
//                      usually newLine
                } else if (statement instanceof IASTLabelStatement) {
                        writeLabelStatement((IASTLabelStatement) statement);
                        newLine = false;
                } else if (statement instanceof IASTCaseStatement) {
                        writeCaseStatement((IASTCaseStatement) statement);
//                      usually newLine                 
                }else if (statement instanceof IASTDefaultStatement) {
                        writeDefaultStatement((IASTDefaultStatement)statement);
                } else if (statement instanceof IASTContinueStatement){
                        writeContinueStatement((IASTContinueStatement)statement);
//                      usually newLine
                } else if (statement instanceof IASTCompoundStatement) {
                        writeCompoundStatement((IASTCompoundStatement) statement);
                        if(compoundNoNewLine){
                                newLine = false;
                                compoundNoNewLine = false;
                        }
                } else if (statement instanceof IASTBreakStatement) {
                        writeBreakStatement((IASTBreakStatement) statement);
//                      usually newLine
                } else if (statement instanceof IASTSwitchStatement) {
                        writeSwitchStatement((IASTSwitchStatement) statement);
                        newLine = false;
                } else if (statement instanceof IASTIfStatement) {
                        writeIfStatement((IASTIfStatement) statement);                  
                        newLine = false;
                } else if (statement instanceof IASTWhileStatement) {
                        writeWhileStatement( (IASTWhileStatement) statement );
                        newLine = false;
                } else if (statement instanceof IASTForStatement) {
                        writeForStatement((IASTForStatement) statement);
                        newLine = false;
                } else if (statement instanceof IASTDoStatement) {
                        writeDoStatement((IASTDoStatement) statement);
                        newLine = true;
                } else if (statement instanceof ICPPASTTryBlockStatement) {
                        writeTryBlockStatement((ICPPASTTryBlockStatement) statement);
                        newLine = false;
                } else if (statement instanceof ICPPASTCatchHandler) {
                        writeCatchHandler((ICPPASTCatchHandler) statement);
                        newLine = false;
                } else if (statement instanceof IASTProblemStatement) {
                        throw new ProblemRuntimeException((IASTProblemStatement)statement);
                } 
                
                if(hasTrailingComments(statement)) {
                        writeTrailingComments(statement, newLine);                      
                }
                else{
                        if(newLine){
                                scribe.newLine();
                        }
                }
                
                return ASTVisitor.PROCESS_SKIP;
        }

        private void writeDoStatement(IASTDoStatement doStatement) {
                nextCompoundNoNewLine();
                
                scribe.print(DO);
                writeBodyStatement(doStatement.getBody(), true);
                scribe.print(DO_WHILE);
                doStatement.getCondition().accept(visitor);
                scribe.print(')');
                scribe.printSemicolon();
        }

        private void writeForStatement(IASTForStatement forStatment) {
                scribe.noNewLines();
                scribe.print(FOR);
                writeStatement(forStatment.getInitializerStatement(),false);
                if (forStatment instanceof ICPPASTForStatement) {
                        ICPPASTForStatement cppForStatment = (ICPPASTForStatement) forStatment;
                        IASTDeclaration cppConditionDeclaration = cppForStatment.getConditionDeclaration();
                        if(cppConditionDeclaration == null) {
                                visitNodeIfNotNull(cppForStatment.getConditionExpression());
                                scribe.printSemicolon();
                        } else {
                                cppConditionDeclaration.accept(visitor);
                        }
                        
                } else {
                        if(forStatment.getConditionExpression() != null) {
                                forStatment.getConditionExpression().accept(visitor);
                                scribe.printSemicolon();
                        }
                }
                
                visitNodeIfNotNull(forStatment.getIterationExpression());
                scribe.print(')');
                scribe.newLines();
                nextCompoundNoNewLine();
                writeBodyStatement(forStatment.getBody(), false);
        }

        private void writeIfStatement(IASTIfStatement ifStatement) {
                scribe.print(IF);
                scribe.noNewLines();
                if (ifStatement instanceof ICPPASTIfStatement) {
                        ICPPASTIfStatement cppIfStatment = (ICPPASTIfStatement) ifStatement;

                        if(cppIfStatment.getConditionDeclaration() == null) {
                                cppIfStatment.getConditionExpression().accept(visitor);
                        } else {
                                writeDeclarationWithoutSemicolon(cppIfStatment.getConditionDeclaration());
                        }
                } else {
                        ifStatement.getConditionExpression().accept(visitor);
                }
                
                scribe.print(')');
                scribe.newLines();
                nextCompoundNoNewLine();
                IASTStatement elseClause = ifStatement.getElseClause();
                writeBodyStatement(ifStatement.getThenClause(), elseClause != null ? true : false);
                
                if(elseClause != null){
                        scribe.print(ELSE);
                        nextCompoundNoNewLine();
                        writeBodyStatement(elseClause, false);
                }
        }

        protected void writeDeclarationWithoutSemicolon(
                        IASTDeclaration declaration) {
                declWriter.writeDeclaration(declaration, false);
        }

        private void writeBreakStatement(IASTBreakStatement statement) {
                scribe.print(BREAK);
                scribe.printSemicolon();
        }

        private void writeContinueStatement(IASTContinueStatement statement) {
                scribe.print(CONTINUE);
                scribe.printSemicolon();
        }

        private void writeLabelStatement(IASTLabelStatement labelStatement) {
                labelStatement.getName().accept(visitor);
                scribe.print(':');
                scribe.newLine();                       
                labelStatement.getNestedStatement().accept(visitor);
        }

        private void writeGotoStatement(IASTGotoStatement gotoStatement) {
                scribe.print(GOTO);
                gotoStatement.getName().accept(visitor);
                scribe.printSemicolon();
        }

        private void writeReturnStatement(IASTReturnStatement returnStatement) {
                scribe.noNewLines();
                scribe.print(RETURN);
                IASTExpression returnValue = returnStatement.getReturnValue();
                if(returnValue != null){
                        scribe.printSpaces(1);
                        returnValue.accept(visitor);
                }
                scribe.newLines();
                scribe.printSemicolon();
        }

        private void writeNullStatement(IASTNullStatement nullStmt) {
                scribe.printSemicolon();
        }
        
        private void writeDeclarationStatement(IASTDeclarationStatement decStmt) {
                decStmt.getDeclaration().accept(visitor);
        }

        private void writeExpressionStatement(IASTExpressionStatement expStmt) {
                expStmt.getExpression().accept(visitor);
                scribe.printSemicolon();
        }

        private void writeCatchHandler(ICPPASTCatchHandler catchStatement) {
                scribe.print(CATCH);
                if (catchStatement.isCatchAll()) {
                        scribe.print(VAR_ARGS);
                } else {
                        scribe.noSemicolon();
                        scribe.noNewLines();
                        catchStatement.getDeclaration().accept(visitor);
                        scribe.newLines();
                }
                scribe.print(')');
                writeBodyStatement(catchStatement.getCatchBody(), true);
        }

        private void writeTryBlockStatement(ICPPASTTryBlockStatement tryStatement) {
                scribe.print(TRY);
                tryStatement.getTryBody().accept(visitor);
                for (ICPPASTCatchHandler catchStatement : tryStatement.getCatchHandlers()) {
                        writeStatement(catchStatement, false);
                }
        }

        private void writeWhileStatement(IASTWhileStatement whileStatment) {
                scribe.print(WHILE);
                scribe.noNewLines();
                if (whileStatment instanceof ICPPASTWhileStatement) {
                        ICPPASTWhileStatement cppWhileStatment = (ICPPASTWhileStatement) whileStatment;
                        if(cppWhileStatment.getConditionDeclaration() == null) {
                                cppWhileStatment.getCondition().accept(visitor);
                        } else {
                                writeDeclarationWithoutSemicolon(cppWhileStatment.getConditionDeclaration());
                        }               
                } else {
                        whileStatment.getCondition().accept(visitor);
                }
                scribe.print(')');
                scribe.newLines();
                nextCompoundNoNewLine();
                writeBodyStatement(whileStatment.getBody(), false);
        }

        private void writeCaseStatement(IASTCaseStatement caseStatement) {
                nextCompoundIndentationLevelOneMore();
                
                if(!switchIsNew){
                        scribe.decrementIndentationLevel();
                }
                scribe.print(CASE);
                caseStatement.getExpression().accept(visitor);
                scribe.print(':');
                scribe.incrementIndentationLevel();
                switchIsNew = false;
        }

        private void writeSwitchStatement(IASTSwitchStatement switchStatement) {
                switchIsNew = true;
                
                scribe.print(SWITCH_BRACKET);
                scribe.noNewLines();
                if (switchStatement instanceof ICPPASTSwitchStatement) {
                        ICPPASTSwitchStatement cppSwitchStatement = (ICPPASTSwitchStatement) switchStatement;
                        if(cppSwitchStatement.getControllerDeclaration() == null) {
                                cppSwitchStatement.getControllerExpression().accept(visitor);
                        } else {
                                declWriter.writeDeclaration(cppSwitchStatement.getControllerDeclaration(), false);
                        }
                } else {
                        switchStatement.getControllerExpression().accept(visitor);
                }
                scribe.print(')');
                scribe.newLines();
                nextCompoundNoNewLine();
                writeBodyStatement(switchStatement.getBody(), false);
                
                switchIsNew = false;
        }

        private void writeDefaultStatement(IASTDefaultStatement defaultStatement) {
                nextCompoundIndentationLevelOneMore();
                
                if(!switchIsNew){
                        scribe.decrementIndentationLevel();
                }
                scribe.print(DEFAULT);
                scribe.incrementIndentationLevel();
                switchIsNew = false;
        }
        
        private void writeCompoundStatement(IASTCompoundStatement compoundStatement) {
                scribe.printLBrace();
                scribe.newLine();
                for (IASTStatement statements : getNestedStatements(compoundStatement)) {
                        statements.accept(visitor);
                }
                
                if(hasFreestandingComments(compoundStatement)) {
                        writeFreeStandingComments(compoundStatement);                   
                }
                
                if(decrementIndentationLevelOneMore){
                        scribe.decrementIndentationLevel();
                        decrementIndentationLevelOneMore = false;
                }
                scribe.printRBrace();
        }

        protected IASTStatement[] getNestedStatements(IASTCompoundStatement compoundStatement) {
                return compoundStatement.getStatements();
        }       
        
        protected void writeBodyStatement(IASTStatement statement, boolean isDoStatement) {
                if (statement instanceof IASTCompoundStatement){
                        //TODO hsr existiert noch eine methode
                        statement.accept(visitor);
                        if(!isDoStatement){
                                scribe.newLine();
                        }
                        compoundNoNewLine = false;
                } else if (statement instanceof IASTNullStatement){
                        statement.accept(visitor);
                        scribe.newLine();
                } else {
                        scribe.incrementIndentationLevel();     
                        scribe.newLine();       
                        statement.accept(visitor);
                        scribe.decrementIndentationLevel();     
                        scribe.newLine();
                }
        }
        
        /**
         * Write no new Line after the next Compound-Statement 
         *
         */
        protected void nextCompoundNoNewLine(){
                compoundNoNewLine = true;
        }
        
        /**
         * Indent one time more at the end (before the closing Brackets) 
         * of a Compound-Statement 
         *
         */
        protected void nextCompoundIndentationLevelOneMore(){
                decrementIndentationLevelOneMore = true;
        }

        protected int writeMixedStatement(IASTStatement statement) {
                //IFile file = FileHelper.getIFilefromIASTNode(statement);
                //int offset = statement.getFileLocation().getNodeOffset();
                //int length = statement.getFileLocation().getNodeLength();
                String code = "???XXX???"; //FileContentHelper.getContent(file, offset, length);
                
                scribe.println(code);
                return ASTVisitor.PROCESS_SKIP;
        }
}


/**
 * 
 * Generates source code of declarator nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTDeclarator
 * @author Emanuel Graf IFS
 * 
 */
class DeclaratorWriter extends NodeWriter {

        private static final String AMPERSAND_SPACE = "& "; //$NON-NLS-1$
        private static final String AMPERSAND__AMPERSAND_SPACE = "&& "; //$NON-NLS-1$
        private static final String STAR_SPACE = "* "; //$NON-NLS-1$
        private static final String PURE_VIRTUAL = " =0"; //$NON-NLS-1$
        
        public DeclaratorWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
        }
        
        protected void writeDeclarator(IASTDeclarator declarator) {
                if (declarator instanceof IASTStandardFunctionDeclarator) {
                        writeFunctionDeclarator((IASTStandardFunctionDeclarator) declarator);
                }else if (declarator instanceof IASTArrayDeclarator) {
                        writeArrayDeclarator((IASTArrayDeclarator) declarator);
                }else if (declarator instanceof IASTFieldDeclarator) {
                        writeFieldDeclarator((IASTFieldDeclarator) declarator);
                }else if (declarator instanceof ICASTKnRFunctionDeclarator) {
                        writeCKnRFunctionDeclarator((ICASTKnRFunctionDeclarator) declarator);
                }else{
                        writeDefaultDeclarator(declarator);
                }
                
                if(hasTrailingComments(declarator)) {
                        writeTrailingComments(declarator, false);                       
                }       
        }

        protected void writeDefaultDeclarator(IASTDeclarator declarator) {
                IASTPointerOperator[] pointOps = declarator.getPointerOperators();
                writePointerOperators(declarator, pointOps);
                IASTName name = declarator.getName();
                name.accept(visitor);
                writeNestedDeclarator(declarator);
                IASTInitializer init = getInitializer(declarator);
                if(init!= null) {
                        init.accept(visitor);
                }
        }

        protected void writePointerOperators(IASTDeclarator declarator, IASTPointerOperator[] pointOps) {
                for (IASTPointerOperator operator : pointOps) {
                        writePointerOp(operator);
                }
        }

        private void writeFunctionDeclarator(IASTStandardFunctionDeclarator funcDec) {
                IASTPointerOperator[] pointOps = funcDec.getPointerOperators();
                writePointerOperators(funcDec, pointOps);
                funcDec.getName().accept(visitor);
                writeNestedDeclarator(funcDec);
                writeParameters(funcDec);
                writeInitializer(funcDec);
                if (funcDec instanceof ICPPASTFunctionDeclarator) {
                        writeCppFunctionDeclarator((ICPPASTFunctionDeclarator) funcDec);
                }
        }

        private void writeInitializer(IASTStandardFunctionDeclarator funcDec) {
                IASTInitializer init = getInitializer(funcDec);
                if(init != null) {
                        init.accept(visitor);
                }
        }

        private void writeParameters(IASTStandardFunctionDeclarator funcDec) {
                IASTParameterDeclaration[] paraDecls = funcDec.getParameters();
                scribe.print('(');
                writeParameterDeclarations(funcDec, paraDecls);
                scribe.print(')');
        }

        private void writeNestedDeclarator(IASTDeclarator funcDec) {
                IASTDeclarator nestedDeclarator = funcDec.getNestedDeclarator();
                if(nestedDeclarator != null) {
                        scribe.print('(');
                        nestedDeclarator.accept(visitor);
                        scribe.print(')');
                }
        }

        private void writeCppFunctionDeclarator(ICPPASTFunctionDeclarator funcDec) {
                if (funcDec.isConst()) {
                        scribe.printSpace();
                        scribe.print(CONST);
                }
                if (funcDec.isVolatile()) {
                        scribe.printSpace();
                        scribe.print(VOLATILE);
                }
                if(funcDec.isPureVirtual()) {
                        scribe.print(PURE_VIRTUAL);
                }
                writeExceptionSpecification(funcDec, funcDec.getExceptionSpecification());
        }

        protected void writeExceptionSpecification(ICPPASTFunctionDeclarator funcDec, IASTTypeId[] exceptions) {
                if (exceptions != ICPPASTFunctionDeclarator.NO_EXCEPTION_SPECIFICATION) {
                        scribe.printSpace();
                        scribe.print(THROW);
                        scribe.print('(');
                        writeNodeList(exceptions);
                        scribe.print(')');
                }
        }

        protected void writeParameterDeclarations(IASTStandardFunctionDeclarator funcDec, IASTParameterDeclaration[] paraDecls) {
                writeNodeList(paraDecls);
                if(funcDec.takesVarArgs()){
                        if(paraDecls.length > 0){
                                scribe.print(COMMA_SPACE);
                        }
                        scribe.print(VAR_ARGS);
                }
        }
        
        private void writePointer(IASTPointer operator) {
                if (operator instanceof ICPPASTPointerToMember) {
                        ICPPASTPointerToMember pointerToMemberOp = (ICPPASTPointerToMember) operator;
                        if(pointerToMemberOp.getName() != null){
                                pointerToMemberOp.getName().accept(visitor);
                                scribe.print(STAR_SPACE);
                        }
                } else {
                        scribe.print('*');
                }
                
                
                if (operator.isConst()) {
                        scribe.printStringSpace(CONST);

                }
                if (operator.isVolatile()) {
                        scribe.printStringSpace(VOLATILE);
                }
                if (operator instanceof ICASTPointer) {
                        ICASTPointer cPoint = (ICASTPointer) operator;
                        if(cPoint.isRestrict()) {
                                scribe.print(RESTRICT);
                        }
                }
                if (operator instanceof IGPPASTPointer) {
                        IGPPASTPointer gppPoint = (IGPPASTPointer) operator;
                        if(gppPoint.isRestrict()) {
                                scribe.print(RESTRICT);
                        }
                }
        }

        private void writePointerOp(IASTPointerOperator operator) {
                if (operator instanceof IASTPointer) {
                        IASTPointer pointOp = (IASTPointer) operator;
                        writePointer(pointOp);
                } else if (operator instanceof ICPPASTReferenceOperator) {
                        if (((ICPPASTReferenceOperator) operator).isRValueReference()) {
                                scribe.print(AMPERSAND__AMPERSAND_SPACE);
                        } else {
                                scribe.print(AMPERSAND_SPACE);
                        }
                }
        }

        private void writeArrayDeclarator(IASTArrayDeclarator arrDecl) {
                IASTPointerOperator[] pointOps = arrDecl.getPointerOperators();
                writePointerOperators(arrDecl, pointOps);
                IASTName name = arrDecl.getName();
                name.accept(visitor);

                writeNestedDeclarator(arrDecl);
                
                IASTArrayModifier[] arrMods = arrDecl.getArrayModifiers();
                writeArrayModifiers(arrDecl, arrMods);
                IASTInitializer initializer = getInitializer(arrDecl);
                if(initializer != null) {
                        initializer.accept(visitor);
                }
        }

        protected IASTInitializer getInitializer(IASTDeclarator decl) {
                return decl.getInitializer();
        }

        protected void writeArrayModifiers(IASTArrayDeclarator arrDecl, IASTArrayModifier[] arrMods) {
                for (IASTArrayModifier modifier : arrMods) {
                        writeArrayModifier(modifier);
                }
        }

        protected void writeArrayModifier(IASTArrayModifier modifier) {
                scribe.print('[');
                IASTExpression ex= modifier.getConstantExpression();
                if (ex != null) {
                        ex.accept(visitor);
                }
                scribe.print(']');
        }

        private void writeFieldDeclarator(IASTFieldDeclarator fieldDecl) {
                IASTPointerOperator[] pointOps = fieldDecl.getPointerOperators();
                writePointerOperators(fieldDecl, pointOps);
                fieldDecl.getName().accept(visitor);
                scribe.printSpace();
                scribe.print(':');
                scribe.printSpace();
                fieldDecl.getBitFieldSize().accept(visitor);
                IASTInitializer initializer = getInitializer(fieldDecl);
                if(initializer != null) {
                        initializer.accept(visitor);
                }
        }

        private void writeCKnRFunctionDeclarator(ICASTKnRFunctionDeclarator knrFunct) {
                knrFunct.getName().accept(visitor);
                scribe.print('(');
                writeKnRParameterNames(knrFunct, knrFunct.getParameterNames());
                scribe.print(')');
                scribe.newLine();
                writeKnRParameterDeclarations(knrFunct, knrFunct.getParameterDeclarations());
                

        }

        protected void writeKnRParameterDeclarations(
                        ICASTKnRFunctionDeclarator knrFunct, IASTDeclaration[] knrDeclarations) {
                for (int i = 0; i < knrDeclarations.length;  ++i) {
                        scribe.noNewLines();
                        knrDeclarations[i].accept(visitor);
                        scribe.newLines();
                        if(i + 1 < knrDeclarations.length) {
                                scribe.newLine();
                        }
                }
        }

        protected void writeKnRParameterNames(ICASTKnRFunctionDeclarator knrFunct, IASTName[] parameterNames) {
                writeNodeList(parameterNames);
        }
}



/**
 * 
 * Generates source code of declaration nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTDeclaration
 * @author Emanuel Graf IFS
 * 
 */
class DeclarationWriter extends NodeWriter{
        
        private static final String ASM_END = ")"; //$NON-NLS-1$
        private static final String ASM_START = "asm("; //$NON-NLS-1$
        private static final String TEMPLATE_DECLARATION = "template<"; //$NON-NLS-1$
        private static final String EXPORT = "export "; //$NON-NLS-1$
        private static final String TEMPLATE_SPECIALIZATION = "template <> "; //$NON-NLS-1$
        private static final String NAMESPACE = "namespace "; //$NON-NLS-1$
        private static final String USING = "using "; //$NON-NLS-1$
        private boolean printSemicolon;
        
        public DeclarationWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
        }
        
        protected void writeDeclaration(IASTDeclaration declaration) throws ProblemRuntimeException{
                writeDeclaration(declaration, true);
        }
        
        protected void writeDeclaration(IASTDeclaration declaration, boolean writeSemicolon) {
                boolean addNewLine = true;
                printSemicolon = writeSemicolon;
                if (declaration instanceof IASTASMDeclaration) {
                        writeASMDeclatation((IASTASMDeclaration) declaration);
                } else if (declaration instanceof IASTFunctionDefinition) {
                        writeFunctionDefinition((IASTFunctionDefinition) declaration);
                } else if (declaration instanceof IASTProblemDeclaration) {
                        throw new ProblemRuntimeException((IASTProblemDeclaration) declaration);
                } else if (declaration instanceof IASTSimpleDeclaration) {
                        writeSimpleDeclaration((IASTSimpleDeclaration) declaration);
                } else if (declaration instanceof ICPPASTExplicitTemplateInstantiation) {
                        writeExplicitTemplateInstantiation((ICPPASTExplicitTemplateInstantiation) declaration);
                        addNewLine = false;
                } else if (declaration instanceof ICPPASTLinkageSpecification) {
                        writeLinkageSpecification((ICPPASTLinkageSpecification) declaration);
                } else if (declaration instanceof ICPPASTNamespaceAlias) {
                        writeNamespaceAlias((ICPPASTNamespaceAlias) declaration); 
                } else if (declaration instanceof ICPPASTTemplateDeclaration) {
                        writeTemplateDeclaration((ICPPASTTemplateDeclaration) declaration);
                        addNewLine = false;
                } else if (declaration instanceof ICPPASTTemplateSpecialization) {
                        writeTemplateSpecialization((ICPPASTTemplateSpecialization) declaration);
                        addNewLine = false;
                } else if (declaration instanceof ICPPASTUsingDeclaration) {
                        writeUsingDeclaration((ICPPASTUsingDeclaration) declaration);
                } else if (declaration instanceof ICPPASTUsingDirective) {
                        writeUsingDirective((ICPPASTUsingDirective) declaration);
                } else if (declaration instanceof ICPPASTVisibilityLabel) {
                        writeVisibilityLabel((ICPPASTVisibilityLabel) declaration);
                }
                
                if(hasTrailingComments(declaration)) {
                        writeTrailingComments(declaration, addNewLine);
                }else if(addNewLine){
                        scribe.newLine();
                }
                if(hasFreestandingComments(declaration)){
                        writeFreeStandingComments(declaration);
                }

                if (declaration instanceof ICPPASTUsingDirective) {
                        scribe.newLine();
                }
        }

        private void writeVisibilityLabel(ICPPASTVisibilityLabel visiblityLabel) {
                scribe.decrementIndentationLevel();
                switch (visiblityLabel.getVisibility()) {
                case ICPPASTVisibilityLabel.v_private:
                        scribe.print(PRIVATE);
                        scribe.print(':');
                        break;
                case ICPPASTVisibilityLabel.v_protected:
                        scribe.print(PROTECTED);
                        scribe.print(':');
                        break;
                case ICPPASTVisibilityLabel.v_public:
                        scribe.print(PUBLIC);   
                        scribe.print(':');
                        break;
                default:
                        return;
                }
                scribe.incrementIndentationLevel();
        }

        private void writeUsingDirective(ICPPASTUsingDirective usingDirective) {
                scribe.print(USING + NAMESPACE);
                usingDirective.getQualifiedName().accept(visitor);
                scribe.printSemicolon();
        }

        private void writeUsingDeclaration(ICPPASTUsingDeclaration usingDeclaration) {
                scribe.print(USING);
                if(usingDeclaration.isTypename()){
                        scribe.print(TYPENAME);
                }
                usingDeclaration.getName().accept(visitor);             
                scribe.printSemicolon();
        }

        private void writeTemplateSpecialization(ICPPASTTemplateSpecialization templateSpecialization) {
                scribe.print(TEMPLATE_SPECIALIZATION);
                templateSpecialization.getDeclaration().accept(visitor);
        }

        protected void writeTemplateDeclaration(ICPPASTTemplateDeclaration templateDeclaration) {
                if(templateDeclaration.isExported()){
                        scribe.print(EXPORT);
                }
                scribe.print(TEMPLATE_DECLARATION);
                ICPPASTTemplateParameter[] paraDecls = templateDeclaration.getTemplateParameters();
                for(int i = 0; i < paraDecls.length; ++i) {
                        paraDecls[i].accept(visitor);
                        if(i + 1 < paraDecls.length) {
                                scribe.print(',');
                                scribe.printSpaces(1);
                        }
                }
                scribe.print('>');
                scribe.printSpace();
                templateDeclaration.getDeclaration().accept(visitor);
        }

        protected void writeDeclaration(ICPPASTNamespaceDefinition declaration){
                printSemicolon = true;
                writeNamespaceDefinition(declaration);
        }
        
        private void writeNamespaceDefinition(ICPPASTNamespaceDefinition namespaceDefinition) {
                scribe.print(NAMESPACE);
                namespaceDefinition.getName().accept(visitor);
                if(!hasTrailingComments(namespaceDefinition.getName())) {
                        scribe.newLine();
                }
                scribe.printLBrace();
                scribe.newLine();
                writeDeclarationsInNamespace(namespaceDefinition, namespaceDefinition.getDeclarations());
                if(hasFreestandingComments(namespaceDefinition)) {
                        writeFreeStandingComments(namespaceDefinition);
                }
                scribe.printRBrace();
                
                if(hasTrailingComments(namespaceDefinition)) {
                        writeTrailingComments(namespaceDefinition);
                }else{
                        scribe.newLine();
                }       
        }

        protected void writeDeclarationsInNamespace(ICPPASTNamespaceDefinition namespaceDefinition, IASTDeclaration[] declarations) {
                for (IASTDeclaration declaration : declarations) {
                        declaration.accept(visitor);
                }
        }

        private void writeNamespaceAlias(ICPPASTNamespaceAlias namespaceAliasDefinition) {
                scribe.print(NAMESPACE);
                namespaceAliasDefinition.getAlias().accept(visitor);
                scribe.print(EQUALS);
                namespaceAliasDefinition.getMappingName().accept(visitor);
                printSemicolon();
        }

        private void writeLinkageSpecification(ICPPASTLinkageSpecification linkageSpecification) {
                scribe.print( EXTERN);
                scribe.print(linkageSpecification.getLiteral());
                scribe.printSpaces(1);
                
                IASTDeclaration[] declarations = linkageSpecification.getDeclarations();
                if(declarations.length > 1){
                        scribe.printLBrace();
                        scribe.decrementIndentationLevel();
                        scribe.newLine();
                        for (IASTDeclaration declaration : declarations) {
                                declaration.accept(visitor);
                        }
                        scribe.printRBrace();
                        scribe.incrementIndentationLevel();
                } else if(declarations.length > 0) {
                        visitNodeIfNotNull(declarations[0]);
                }
        }

        private void writeExplicitTemplateInstantiation(ICPPASTExplicitTemplateInstantiation explicitTemplateInstantiation) {
                switch(explicitTemplateInstantiation.getModifier()){
                case ICPPASTExplicitTemplateInstantiation.EXTERN:
                        scribe.print(EXTERN);
                        break;
                case ICPPASTExplicitTemplateInstantiation.INLINE:
                        scribe.print(INLINE);
                        break;
                case ICPPASTExplicitTemplateInstantiation.STATIC:
                        scribe.print(STATIC);
                        break;
                }
                
                scribe.print(TEMPLATE);
                explicitTemplateInstantiation.getDeclaration().accept(visitor);
        }

        private void writeASMDeclatation(IASTASMDeclaration asmDeclaration) {
                scribe.print(ASM_START);
                scribe.print(asmDeclaration.getAssembly());
                scribe.print(ASM_END);
                printSemicolon();
        }

        private void printSemicolon() {
                if(printSemicolon) {
                        scribe.printSemicolon();
                }
        }

        private void writeFunctionDefinition(IASTFunctionDefinition funcDef) {
                IASTDeclSpecifier declSpecifier = funcDef.getDeclSpecifier();
                declSpecifier.accept(visitor);
                if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
                        IASTSimpleDeclSpecifier simDeclSpec = (IASTSimpleDeclSpecifier) declSpecifier;
                        if(simDeclSpec.getType() != IASTSimpleDeclSpecifier.t_unspecified) {
                                scribe.printSpace();
                        }
                }else {
                        scribe.printSpace();
                }
                IASTDeclarator declarator = ASTQueries.findOutermostDeclarator(funcDef.getDeclarator());
                declarator.accept(visitor);
                
                if (funcDef instanceof ICPPASTFunctionWithTryBlock) {
                        scribe.newLine();
                        scribe.print(Keywords.TRY);
                }
                
                if (funcDef instanceof ICPPASTFunctionDefinition) {
                        ICPPASTFunctionDefinition cppFuncDef= (ICPPASTFunctionDefinition) funcDef;
                        writeCtorChainInitializer(cppFuncDef, cppFuncDef.getMemberInitializers());
                }
                scribe.newLine();

                funcDef.getBody().accept(visitor);
                
                if (funcDef instanceof ICPPASTFunctionWithTryBlock) {
                        ICPPASTFunctionWithTryBlock tryblock = (ICPPASTFunctionWithTryBlock) funcDef;
                        ICPPASTCatchHandler[] catches = tryblock.getCatchHandlers();
                        for (ICPPASTCatchHandler handler : catches) {
                                handler.accept(visitor);
                        }
                }
        }
        
        protected void writeCtorChainInitializer(
                        ICPPASTFunctionDefinition funcDec, ICPPASTConstructorChainInitializer[] ctorInitChain) {
                if(ctorInitChain.length != 0) {
                        scribe.newLine();
                        scribe.print(':');
                }
                for(int i = 0; i < ctorInitChain.length; ++i) {
                        ICPPASTConstructorChainInitializer initializer = ctorInitChain[i];
                        initializer.accept(visitor);
                        if(i+1 < ctorInitChain.length) {
                                scribe.print(COMMA_SPACE);
                        }
                }
        }

        private void writeSimpleDeclaration(IASTSimpleDeclaration simpDec) {
                IASTDeclSpecifier declSpecifier = simpDec.getDeclSpecifier();
                IASTDeclarator[] decls = simpDec.getDeclarators();
                                                
                declSpecifier.accept(visitor);
                boolean noSpace = false;
                if (declSpecifier instanceof IASTSimpleDeclSpecifier) {
                        IASTSimpleDeclSpecifier simpleDeclSpecifier = (IASTSimpleDeclSpecifier) declSpecifier;
                        if(simpleDeclSpecifier.getType() == IASTSimpleDeclSpecifier.t_unspecified) {
                                noSpace = true;
                        }
                }
                
                if(decls.length > 0) {
                        if(!noSpace) {
                                scribe.printSpace();
                        }
                        writeNodeList(decls);
                }
                
                printSemicolon();
        }

}



/**
 * 
 * Generates source code of initializer nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTInitializer
 * @author Emanuel Graf IFS
 * 
 */
class InitializerWriter extends NodeWriter{

        public InitializerWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
        }
        
        protected void writeInitializer(IASTInitializer initializer) {
                if (initializer instanceof IASTEqualsInitializer) {
                        writeEqualsInitializer((IASTEqualsInitializer) initializer);
                }else if (initializer instanceof IASTInitializerList) {
                        writeInitializerList((IASTInitializerList) initializer);
                }else if (initializer instanceof ICPPASTConstructorInitializer) {
                        writeConstructorInitializer((ICPPASTConstructorInitializer) initializer);
                }else if (initializer instanceof ICASTDesignatedInitializer) {
                        writeDesignatedInitializer((ICASTDesignatedInitializer) initializer);
                }else if (initializer instanceof ICPPASTConstructorChainInitializer) {
                        writeConstructorChainInitializer((ICPPASTConstructorChainInitializer) initializer);
                }
                if (hasTrailingComments(initializer))
                        writeTrailingComments(initializer, false);
        }

        
        private void writeEqualsInitializer(IASTEqualsInitializer initializer) {
                scribe.print(EQUALS);
                IASTInitializerClause init = initializer.getInitializerClause();
                if (init != null) {
                        init.accept(visitor);
                }
        }

        private void writeConstructorChainInitializer(ICPPASTConstructorChainInitializer initializer) {
                initializer.getMemberInitializerId().accept(visitor);
                initializer.getInitializer().accept(visitor);
        }

        private void writeInitializerList(IASTInitializerList initList) {
                scribe.printLBrace();
                IASTInitializerClause[] inits = initList.getClauses();
                writeNodeList(inits);
                scribe.printRBrace();
        }

        private void writeConstructorInitializer(ICPPASTConstructorInitializer ctorInit) {
                scribe.print('(');
                writeNodeList(ctorInit.getArguments());
                scribe.print(')');              
        }

        private void writeDesignatedInitializer(ICASTDesignatedInitializer desigInit) {
                ICASTDesignator[] designators =  desigInit.getDesignators();
                for (ICASTDesignator designator : designators) {
                        writeDesignator(designator);
                }
                scribe.print(EQUALS);
                desigInit.getOperand().accept(visitor);
        }

        private void writeDesignator(ICASTDesignator designator) {
                if (designator instanceof ICASTFieldDesignator) {
                        ICASTFieldDesignator fieldDes = (ICASTFieldDesignator) designator;
                        scribe.print('.');
                        fieldDes.getName().accept(visitor);
                }else if (designator instanceof ICASTArrayDesignator) {
                        ICASTArrayDesignator arrDes = (ICASTArrayDesignator) designator;
                        scribe.print('[');
                        arrDes.getSubscriptExpression().accept(visitor);
                        scribe.print(']');
                }else if (designator instanceof IGCCASTArrayRangeDesignator) {
                        //IGCCASTArrayRangeDesignator new_name = (IGCCASTArrayRangeDesignator) designator;
                        //TODO IGCCASTArrayRangeDesignator Bespiel zu parsen bringen
                        throw new UnsupportedOperationException("Writing of GCC ArrayRangeDesignator is not yet implemented"); //$NON-NLS-1$
                }
                
        }
}




/**
 * 
 * Generates source code of name nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see IASTName
 * @author Emanuel Graf IFS
 * 
 */
class NameWriter extends NodeWriter {

        private static final String OPERATOR = "operator "; //$NON-NLS-1$


        /**
         * @param scribe
         * @param visitor
         */
        public NameWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
        }
        
        protected void writeName(IASTName name) {
                if (name instanceof ICPPASTTemplateId) {
                        writeTempalteId((ICPPASTTemplateId) name);
                } else if (name instanceof ICPPASTConversionName) {
                        scribe.print(OPERATOR);
                        ((ICPPASTConversionName)name).getTypeId().accept(visitor);
                } else if (name instanceof ICPPASTQualifiedName){
                        writeQualifiedName((ICPPASTQualifiedName) name);
                } else {
                        scribe.print(name.toString());
                }
                
                if(hasTrailingComments(name)) {
                        writeTrailingComments(name);                    
                }               
        }
        
        private void writeTempalteId(ICPPASTTemplateId tempId) {
                if(needsTemplateQualifier(tempId)) {
                        scribe.print(TEMPLATE);
                }
                scribe.print(tempId.getTemplateName().toString());
                scribe.print('<');
                IASTNode[] nodes = tempId.getTemplateArguments();
                for (int i = 0; i < nodes.length; ++i) {
                        nodes[i].accept(visitor);
                        if(i + 1 < nodes.length) {
                                scribe.print(',');
                        }
                }
                scribe.print('>');
                if(isNestedTemplateId(tempId)) {
                        scribe.printSpace();
                }
        }
        
        private boolean needsTemplateQualifier(ICPPASTTemplateId templId){
                if (templId.getParent() instanceof ICPPASTQualifiedName) {
                        ICPPASTQualifiedName qName = (ICPPASTQualifiedName)  templId.getParent();
                        return isDependentName(qName, templId);                 
                }
                return false;
        }
        
        private boolean isDependentName(ICPPASTQualifiedName qname, ICPPASTTemplateId tempId) {
                IASTName[] names = qname.getNames();
                int i = 0;
                for(;i < names.length; ++i){
                        if(names[i] == tempId){
                                return isDependentName(qname, tempId, i);
                        }
                }
                return false;
        }

        private boolean isDependentName(ICPPASTQualifiedName qname,
                        ICPPASTTemplateId tempId, int i) {
                if(i <= 0){
                        return false;
                }
                if (qname.getNames()[i-1] instanceof ICPPASTTemplateId) {
                        return true;
                }
                IBinding binding = qname.getNames()[i-1].resolveBinding();
                if (binding instanceof CPPTemplateTypeParameter) {
                        return true;
                }
                return isDependentName(qname, tempId, i-1);
        }

        private boolean isNestedTemplateId(IASTNode node) {
                while((node = node.getParent()) != null) {
                        if (node instanceof ICPPASTTemplateId) {
                                return true;
                        }
                }
                return false;
        }


        private void writeQualifiedName(ICPPASTQualifiedName qname) {
                IASTName[] nodes = qname.getNames();
                for (int i = 0; i < nodes.length; ++i) {
                        nodes[i].accept(visitor);
                        if(i + 1 < nodes.length) {
                                scribe.print(COLON_COLON);
                        }
                }
        }
}



/**
 * 
 * Generates source code of template parameter nodes. The actual string operations are delegated
 * to the <code>Scribe</code> class.
 * 
 * @see Scribe
 * @see ICPPASTTemplateParameter
 * @author Emanuel Graf IFS
 * 
 */
class TemplateParameterWriter extends NodeWriter {

        private static final String GREATER_THAN_CLASS = "> class"; //$NON-NLS-1$
        private static final String TEMPLATE_LESS_THAN = "template <"; //$NON-NLS-1$



        /**
         * @param scribe
         * @param visitor
         */
        public TemplateParameterWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super(scribe, visitor, commentMap);
        }
        
        protected void writeTemplateParameter(ICPPASTTemplateParameter parameter) {
                if (parameter instanceof ICPPASTParameterDeclaration) {
                        ((IASTParameterDeclaration)((ICPPASTParameterDeclaration) parameter)).accept(visitor);
                } else if (parameter instanceof ICPPASTSimpleTypeTemplateParameter) {
                        writeSimpleTypeTemplateParameter((ICPPASTSimpleTypeTemplateParameter) parameter);
                } else if (parameter instanceof ICPPASTTemplatedTypeTemplateParameter) {
                        writeTemplatedTypeTemplateParameter((ICPPASTTemplatedTypeTemplateParameter) parameter);
                }
        }


        private void writeTemplatedTypeTemplateParameter(ICPPASTTemplatedTypeTemplateParameter templated) {
                scribe.print(TEMPLATE_LESS_THAN);
                
                
                ICPPASTTemplateParameter[] params = templated.getTemplateParameters();
                writeNodeList(params);
                
                scribe.print(GREATER_THAN_CLASS);
                
                if(templated.getName()!=null){
                        scribe.printSpace();
                        templated.getName().accept(visitor);
                }
                
                if(templated.getDefaultValue() != null){
                        scribe.print(EQUALS);
                        templated.getDefaultValue().accept(visitor);
                }
        }



        private void writeSimpleTypeTemplateParameter(ICPPASTSimpleTypeTemplateParameter simple) {
                switch (simple.getParameterType()) {
                case ICPPASTSimpleTypeTemplateParameter.st_class:
                        scribe.print(CLASS_SPACE);
                        break;
                case ICPPASTSimpleTypeTemplateParameter.st_typename:
                        scribe.print(TYPENAME);
                        break;
                }
                                        
                visitNodeIfNotNull(simple.getName());
                
                if(simple.getDefaultType() != null){
                        scribe.print(EQUALS);
                        simple.getDefaultType().accept(visitor);
                }
        }
}



/**
 * 
 * Recognizes nodes that are the result of an macro expansion and replaces them 
 * with a suitable macro call.
 * @author Emanuel Graf IFS
 *
 */
class MacroExpansionHandler {
        
        private int lastMacroExpOffset;
        private final Scribe scribe;
        private IASTTranslationUnit tu;
        private Map<String, List<IIndexName>> macroExpansion = new TreeMap<String, List<IIndexName>>();

        public MacroExpansionHandler(Scribe scribe) {
                this.scribe = scribe;
        }

        protected boolean checkisMacroExpansionNode(IASTNode node) {
                return checkisMacroExpansionNode(node, true);
        }

        protected boolean isStatementWithMixedLocation(IASTStatement node) {
                if(node.getNodeLocations() != null && node.getNodeLocations().length > 1) {
                        for (IASTNodeLocation loc : node.getNodeLocations()) {
                                if (loc instanceof IASTMacroExpansionLocation) {
                                        return true;
                                }
                        }
                }
                return false;
        }

        protected boolean macroExpansionAlreadyPrinted(IASTNode node) {
                IASTNodeLocation[] locs = node.getNodeLocations();
                if(locs.length ==1) {
                        if (locs[0] instanceof IASTMacroExpansionLocation) {
                                IASTMacroExpansionLocation macroNode = (IASTMacroExpansionLocation) locs[0];
                                if (macroNode.asFileLocation().getNodeOffset() == lastMacroExpOffset) {
                                        return true;
                                }
                        }
                }
                return false;
        }

        protected boolean checkisMacroExpansionNode(IASTNode node, boolean write) {
                IASTTranslationUnit unit = node.getTranslationUnit();
                if(tu == null || !tu.equals(unit)) {
                        initEmptyMacros(unit);
                }
                IASTNodeLocation[] locs = node.getNodeLocations();
                if (locs != null && locs.length ==1) {
                        if (locs[0] instanceof IASTMacroExpansionLocation) {
                                IASTMacroExpansionLocation macroNode = (IASTMacroExpansionLocation) locs[0];
        
                                if (macroNode.asFileLocation().getNodeOffset() == lastMacroExpOffset) {
                                        return true;
                                }
                                if (write) {
                                        lastMacroExpOffset = macroNode.asFileLocation().getNodeOffset();
                                        scribe.print(node.getRawSignature());
                                }
                                return true;

                        }
                }
                handleEmptyMacroExpansion(node);
                return false;
        }
        
        private void handleEmptyMacroExpansion(IASTNode node) {
                if(node.getTranslationUnit() == null)return;
                String file = node.getContainingFilename();
                List<IIndexName> exps = macroExpansion.get(file);
                if(exps != null && !exps.isEmpty()) {
                        IASTFileLocation fileLocation = node.getFileLocation();
                        if(fileLocation != null) {
                                int nOff = fileLocation.getNodeOffset();
                                for (IIndexName iIndexName : exps) {
                                        if (iIndexName instanceof PDOMMacroReferenceName) {
                                                PDOMMacroReferenceName mName = (PDOMMacroReferenceName) iIndexName;
                                                int eOff = mName.getFileLocation().getNodeOffset();
                                                int eLength = mName.getFileLocation().getNodeLength();
                                                if(eOff < nOff && Math.abs((eOff+eLength-nOff)) < 3) {
                                                        scribe.print(mName.toString() + " "); //$NON-NLS-1$
                                                }
                                        }
                                }
                        }
                }
                
        }

        private void initEmptyMacros(IASTTranslationUnit unit) {
                if (unit != null) {
                        tu = unit;
                        IIndex index = tu.getIndex();
                        if(index != null) {
                                macroExpansion = new TreeMap<String, List<IIndexName>>();
                                IASTPreprocessorMacroDefinition[] md = tu.getMacroDefinitions();
                                
                                TreeSet<String>paths = new TreeSet<String>();
                                for(IASTPreprocessorIncludeStatement is :tu.getIncludeDirectives()) {
                                        if(!is.isSystemInclude()) {
                                                paths.add(is.getContainingFilename());
                                        }
                                }
                                paths.add(tu.getContainingFilename());
                                
                                for (IASTPreprocessorMacroDefinition iastPreprocessorMacroDefinition : md) {
                                        if(iastPreprocessorMacroDefinition.getExpansion().length() == 0) {
                                                try {
                                                        IIndexMacro[] macroBinding = index.findMacros(iastPreprocessorMacroDefinition.getName().toCharArray(), IndexFilter.ALL, null);
                                                        if(macroBinding.length > 0) {
                                                                IIndexName[] refs = index.findReferences(macroBinding[0]);
                                                                for (IIndexName iIndexName : refs) {
                                                                        String filename2 = iIndexName.getFileLocation().getFileName();
                                                                        List<IIndexName>fileList = macroExpansion.get(filename2);
                                                                        if (paths.contains(filename2)) {
                                                                                if(fileList == null) {
                                                                                        fileList = new ArrayList<IIndexName>();
                                                                                        macroExpansion.put(filename2, fileList);
                                                                                }
                                                                                fileList.add(iIndexName);
                                                                        }
                                                                }
                                                        }
                                                } catch (CoreException e) {
                                                        e.printStackTrace();
                                                }
                                        }
                                }
                        }else {
                                macroExpansion = Collections.emptyMap();
                        }
                }
        }

        public void reset(){
                lastMacroExpOffset = -1;
        }

}



/**
 * 
 * Base class for node writers. This class contains methods and string constants
 * used by multiple node writers.
 * 
 * @author Emanuel Graf IFS
 * 
 */
class NodeWriter {

        protected Scribe scribe;
        protected CPPASTVisitor visitor;
        protected NodeCommentMap commentMap;
        protected static final String COMMA_SPACE = ", "; //$NON-NLS-1$
        protected static final String EQUALS = " = "; //$NON-NLS-1$
        protected static final String RESTRICT = "restrict "; //$NON-NLS-1$
        protected static final String TYPENAME = "typename "; //$NON-NLS-1$
        protected static final String PUBLIC = "public"; //$NON-NLS-1$
        protected static final String PRIVATE = "private"; //$NON-NLS-1$
        protected static final String PROTECTED = "protected"; //$NON-NLS-1$
        protected static final String CONST = "const"; //$NON-NLS-1$
        protected static final String VOLATILE = "volatile"; //$NON-NLS-1$
        protected static final String INLINE = "inline "; //$NON-NLS-1$
        protected static final String EXTERN = "extern "; //$NON-NLS-1$
        protected static final String STATIC = "static "; //$NON-NLS-1$
        protected static final String THROW = "throw "; //$NON-NLS-1$
        protected static final String SPACE_COLON_SPACE = " : "; //$NON-NLS-1$
        protected static final String TEMPLATE = "template "; //$NON-NLS-1$
        protected static final String DOUBLE = "double"; //$NON-NLS-1$
        protected static final String FLOAT = "float"; //$NON-NLS-1$
        protected static final String INT = "int"; //$NON-NLS-1$
        protected static final String CHAR = "char"; //$NON-NLS-1$
        protected static final String VOID = "void"; //$NON-NLS-1$
        protected static final String WCHAR_T = "wchar_t"; //$NON-NLS-1$
        protected static final String CPP_BOOL = "bool"; //$NON-NLS-1$
        protected static final String LONG = "long"; //$NON-NLS-1$
        protected static final String SHORT = "short"; //$NON-NLS-1$
        protected static final String UNSIGNED = "unsigned"; //$NON-NLS-1$
        protected static final String SIGNED = "signed"; //$NON-NLS-1$
        protected static final String CLASS_SPACE = "class "; //$NON-NLS-1$
        protected static final String VAR_ARGS = "..."; //$NON-NLS-1$
        protected static final String COLON_COLON = "::"; //$NON-NLS-1$

        public NodeWriter(Scribe scribe, CPPASTVisitor visitor, NodeCommentMap commentMap) {
                super();
                this.scribe = scribe;
                this.visitor = visitor;
                this.commentMap = commentMap;
        }

        protected void writeNodeList(IASTNode[] nodes) {
                for(int i = 0; i < nodes.length; ++i) {
                        nodes[i].accept(visitor);
                        if(i + 1 < nodes.length) {
                                scribe.print(COMMA_SPACE);
                        }
                }
        }
        
        protected void visitNodeIfNotNull(IASTNode node){
                if(node != null){
                        node.accept(visitor);
                }
        }


        protected void writeTrailingComments(IASTNode node) {
                //default write newLine
                writeTrailingComments(node, true);
        }
        
        protected boolean hasTrailingComments(IASTNode node){
                if(commentMap.getTrailingCommentsForNode(node).size()>0) {
                        return true;
                }
                return false;
        }
        
        protected void writeTrailingComments(IASTNode node, boolean newLine) {
                for(IASTComment comment : commentMap.getTrailingCommentsForNode(node)) {
                        scribe.printSpace();
                        scribe.print(comment.getComment());
                        if(newLine) {
                                scribe.newLine();
                        }
                }
        }

        protected boolean hasFreestandingComments(IASTNode node){
                if(commentMap.getFreestandingCommentsForNode(node).size()>0) {
                        return true;
                }
                return false;
        }

        protected void writeFreeStandingComments(IASTNode node) {
                for(IASTComment comment : commentMap.getFreestandingCommentsForNode(node)) {
                        scribe.print(comment.getComment());
                        scribe.newLine();
                }
        }
}
