// Generated from org\checkerframework\checker\mungo\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.*;
import static org.checkerframework.checker.mungo.typestate.Position.tokenToPos;
import static org.checkerframework.checker.mungo.typestate.Utils.map;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TypestateLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.8", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, DROP=17, 
		END=18, ID=19, WS=20, BlockComment=21, LineComment=22;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "T__10", "T__11", "T__12", "T__13", "T__14", "T__15", "DROP", 
			"END", "ID", "WS", "BlockComment", "LineComment"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'.'", "'package'", "';'", "'import'", "'static'", "'*'", "'typestate'", 
			"'{'", "'}'", "'='", "','", "':'", "'('", "')'", "'<'", "'>'", "'drop'", 
			"'end'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, "DROP", "END", "ID", "WS", "BlockComment", 
			"LineComment"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public TypestateLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Typestate.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\30\u009b\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\3\2\3\2\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6"+
		"\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3"+
		"\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20"+
		"\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\24\6\24r\n\24"+
		"\r\24\16\24s\3\24\7\24w\n\24\f\24\16\24z\13\24\3\25\6\25}\n\25\r\25\16"+
		"\25~\3\25\3\25\3\26\3\26\3\26\3\26\7\26\u0087\n\26\f\26\16\26\u008a\13"+
		"\26\3\26\3\26\3\26\3\26\3\26\3\27\3\27\3\27\3\27\7\27\u0095\n\27\f\27"+
		"\16\27\u0098\13\27\3\27\3\27\3\u0088\2\30\3\3\5\4\7\5\t\6\13\7\r\b\17"+
		"\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26+"+
		"\27-\30\3\2\6\6\2&&C\\aac|\7\2&&\62;C\\aac|\5\2\13\f\17\17\"\"\4\2\f\f"+
		"\17\17\2\u009f\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3"+
		"\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2"+
		"\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3"+
		"\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2"+
		"\2\2\3/\3\2\2\2\5\61\3\2\2\2\79\3\2\2\2\t;\3\2\2\2\13B\3\2\2\2\rI\3\2"+
		"\2\2\17K\3\2\2\2\21U\3\2\2\2\23W\3\2\2\2\25Y\3\2\2\2\27[\3\2\2\2\31]\3"+
		"\2\2\2\33_\3\2\2\2\35a\3\2\2\2\37c\3\2\2\2!e\3\2\2\2#g\3\2\2\2%l\3\2\2"+
		"\2\'q\3\2\2\2)|\3\2\2\2+\u0082\3\2\2\2-\u0090\3\2\2\2/\60\7\60\2\2\60"+
		"\4\3\2\2\2\61\62\7r\2\2\62\63\7c\2\2\63\64\7e\2\2\64\65\7m\2\2\65\66\7"+
		"c\2\2\66\67\7i\2\2\678\7g\2\28\6\3\2\2\29:\7=\2\2:\b\3\2\2\2;<\7k\2\2"+
		"<=\7o\2\2=>\7r\2\2>?\7q\2\2?@\7t\2\2@A\7v\2\2A\n\3\2\2\2BC\7u\2\2CD\7"+
		"v\2\2DE\7c\2\2EF\7v\2\2FG\7k\2\2GH\7e\2\2H\f\3\2\2\2IJ\7,\2\2J\16\3\2"+
		"\2\2KL\7v\2\2LM\7{\2\2MN\7r\2\2NO\7g\2\2OP\7u\2\2PQ\7v\2\2QR\7c\2\2RS"+
		"\7v\2\2ST\7g\2\2T\20\3\2\2\2UV\7}\2\2V\22\3\2\2\2WX\7\177\2\2X\24\3\2"+
		"\2\2YZ\7?\2\2Z\26\3\2\2\2[\\\7.\2\2\\\30\3\2\2\2]^\7<\2\2^\32\3\2\2\2"+
		"_`\7*\2\2`\34\3\2\2\2ab\7+\2\2b\36\3\2\2\2cd\7>\2\2d \3\2\2\2ef\7@\2\2"+
		"f\"\3\2\2\2gh\7f\2\2hi\7t\2\2ij\7q\2\2jk\7r\2\2k$\3\2\2\2lm\7g\2\2mn\7"+
		"p\2\2no\7f\2\2o&\3\2\2\2pr\t\2\2\2qp\3\2\2\2rs\3\2\2\2sq\3\2\2\2st\3\2"+
		"\2\2tx\3\2\2\2uw\t\3\2\2vu\3\2\2\2wz\3\2\2\2xv\3\2\2\2xy\3\2\2\2y(\3\2"+
		"\2\2zx\3\2\2\2{}\t\4\2\2|{\3\2\2\2}~\3\2\2\2~|\3\2\2\2~\177\3\2\2\2\177"+
		"\u0080\3\2\2\2\u0080\u0081\b\25\2\2\u0081*\3\2\2\2\u0082\u0083\7\61\2"+
		"\2\u0083\u0084\7,\2\2\u0084\u0088\3\2\2\2\u0085\u0087\13\2\2\2\u0086\u0085"+
		"\3\2\2\2\u0087\u008a\3\2\2\2\u0088\u0089\3\2\2\2\u0088\u0086\3\2\2\2\u0089"+
		"\u008b\3\2\2\2\u008a\u0088\3\2\2\2\u008b\u008c\7,\2\2\u008c\u008d\7\61"+
		"\2\2\u008d\u008e\3\2\2\2\u008e\u008f\b\26\2\2\u008f,\3\2\2\2\u0090\u0091"+
		"\7\61\2\2\u0091\u0092\7\61\2\2\u0092\u0096\3\2\2\2\u0093\u0095\n\5\2\2"+
		"\u0094\u0093\3\2\2\2\u0095\u0098\3\2\2\2\u0096\u0094\3\2\2\2\u0096\u0097"+
		"\3\2\2\2\u0097\u0099\3\2\2\2\u0098\u0096\3\2\2\2\u0099\u009a\b\27\2\2"+
		"\u009a.\3\2\2\2\b\2sx~\u0088\u0096\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}