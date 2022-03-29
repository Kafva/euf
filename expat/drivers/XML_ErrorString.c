#include <stdlib.h>

// Required!
#include "expat.h" // Has the decleration for types 
									 // and the new version of XML_ErrorString
const XML_LChar *XMLCALL
XML_ErrorString_old_b026324c6904b2a(enum XML_Error code);

int euf_main(){
	#ifdef CBMC
	enum XML_Error code = nondet_int();
	XML_LChar out1 = XML_ErrorString(code);
	XML_LChar out2 = XML_ErrorString_old_b026324c6904b2a(code);

	__CPROVER_assert(out1 == out2, "Equivalent output");
	#endif

	return 0;
}


#if 0
const XML_LChar *XMLCALL
XML_ErrorString_old_b026324c6904b2a(enum XML_Error code) {
  switch (code) {
  case XML_ERROR_NONE:
    return NULL;
  case XML_ERROR_NO_MEMORY:
    return XML_L("out of memory");
  case XML_ERROR_SYNTAX:
    return XML_L("syntax error");
  case XML_ERROR_NO_ELEMENTS:
    return XML_L("no element found");
  case XML_ERROR_INVALID_TOKEN:
    return XML_L("not well-formed (invalid token)");
  case XML_ERROR_UNCLOSED_TOKEN:
    return XML_L("unclosed token");
  case XML_ERROR_PARTIAL_CHAR:
    return XML_L("partial character");
  case XML_ERROR_TAG_MISMATCH:
    return XML_L("mismatched tag");
  case XML_ERROR_DUPLICATE_ATTRIBUTE:
    return XML_L("duplicate attribute");
  case XML_ERROR_JUNK_AFTER_DOC_ELEMENT:
    return XML_L("junk after document element");
  case XML_ERROR_PARAM_ENTITY_REF:
    return XML_L("illegal parameter entity reference");
  case XML_ERROR_UNDEFINED_ENTITY:
    return XML_L("undefined entity");
  case XML_ERROR_RECURSIVE_ENTITY_REF:
    return XML_L("recursive entity reference");
  case XML_ERROR_ASYNC_ENTITY:
    return XML_L("asynchronous entity");
  case XML_ERROR_BAD_CHAR_REF:
    return XML_L("reference to invalid character number");
  case XML_ERROR_BINARY_ENTITY_REF:
    return XML_L("reference to binary entity");
  case XML_ERROR_ATTRIBUTE_EXTERNAL_ENTITY_REF:
    return XML_L("reference to external entity in attribute");
  case XML_ERROR_MISPLACED_XML_PI:
    return XML_L("XML or text declaration not at start of entity");
  case XML_ERROR_UNKNOWN_ENCODING:
    return XML_L("unknown encoding");
  case XML_ERROR_INCORRECT_ENCODING:
    return XML_L("encoding specified in XML declaration is incorrect");
  case XML_ERROR_UNCLOSED_CDATA_SECTION:
    return XML_L("unclosed CDATA section");
  case XML_ERROR_EXTERNAL_ENTITY_HANDLING:
    return XML_L("error in processing external entity reference");
  case XML_ERROR_NOT_STANDALONE:
    return XML_L("document is not standalone");
  case XML_ERROR_UNEXPECTED_STATE:
    return XML_L("unexpected parser state - please send a bug report");
  case XML_ERROR_ENTITY_DECLARED_IN_PE:
    return XML_L("entity declared in parameter entity");
  case XML_ERROR_FEATURE_REQUIRES_XML_DTD:
    return XML_L("requested feature requires XML_DTD support in Expat");
  case XML_ERROR_CANT_CHANGE_FEATURE_ONCE_PARSING:
    return XML_L("cannot change setting once parsing has begun");
  /* Added in 1.95.7. */
  case XML_ERROR_UNBOUND_PREFIX:
    return XML_L("unbound prefix");
  /* Added in 1.95.8. */
  case XML_ERROR_UNDECLARING_PREFIX:
    return XML_L("must not undeclare prefix");
  case XML_ERROR_INCOMPLETE_PE:
    return XML_L("incomplete markup in parameter entity");
  case XML_ERROR_XML_DECL:
    return XML_L("XML declaration not well-formed");
  case XML_ERROR_TEXT_DECL:
    return XML_L("text declaration not well-formed");
  case XML_ERROR_PUBLICID:
    return XML_L("illegal character(s) in public id");
  case XML_ERROR_SUSPENDED:
    return XML_L("parser suspended");
  case XML_ERROR_NOT_SUSPENDED:
    return XML_L("parser not suspended");
  case XML_ERROR_ABORTED:
    return XML_L("parsing aborted");
  case XML_ERROR_FINISHED:
    return XML_L("parsing finished");
  case XML_ERROR_SUSPEND_PE:
    return XML_L("cannot suspend in external parameter entity");
  /* Added in 2.0.0. */
  case XML_ERROR_RESERVED_PREFIX_XML:
    return XML_L(
        "reserved prefix (xml) must not be undeclared or bound to another namespace name");
  case XML_ERROR_RESERVED_PREFIX_XMLNS:
    return XML_L("reserved prefix (xmlns) must not be declared or undeclared");
  case XML_ERROR_RESERVED_NAMESPACE_URI:
    return XML_L(
        "prefix must not be bound to one of the reserved namespace names");
  /* Added in 2.2.5. */
  case XML_ERROR_INVALID_ARGUMENT: /* Constant added in 2.2.1, already */
    return XML_L("invalid argument");
    /* Added in 2.3.0. */
  case XML_ERROR_NO_BUFFER:
    return XML_L(
        "a successful prior call to function XML_GetBuffer is required");
  /* Added in 2.4.0. */
  case XML_ERROR_AMPLIFICATION_LIMIT_BREACH:
    return XML_L(
        "limit on input amplification factor (from DTD and entities) breached");
  }
  return NULL;
}
#endif
