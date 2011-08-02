/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is mozilla.org code.
 *
 * The Initial Developer of the Original Code is
 * The Mozilla Foundation.
 * Portions created by the Initial Developer are Copyright (C) 2011
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Andrew McCreight, Mozilla Corporation
 *   David Mandelin, Mozilla Corporation
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */


/** 
 * Dehydra library script
 * Functions for cycle collection audit scripts
 */

"use strict";


// Generic Dehydra utilities


let DEBUG_PRINT = true;


/**
 * Function for generating error output. The version with the prefix
 * is used to allow output to be easily collected from a mixed file.
 */
function tprint(s) {
  print(s);
  //print("CCANALYZE: " + s);
}

function debug_print(s) {
  if (DEBUG_PRINT)
    tprint("DEBUG>> " + s);
}



/**
 * Dump a Dehydra object in a readable tree format.
 *   o        object to dump
 *   indent   number of spaces to indent by
 *   depth    max nesting depth to dump
 *
 * Printing Dehydra objects tends to produce a big messy JSON-like
 * notation that's hard to read. This flattens things out and doesn't
 * go too deep, in order to reduce the amount of stuff to look at.
 */
function do_dehydra_dump(o, indent, depth) {
  if (depth == 0) return;

  for (let [k, v] in Iterator(o)) {
    if (typeof v == "string") {
      print_indented(k + ": '" + v + "'", indent);
    } else if (typeof v == "number") {
      print_indented(k + ": " + v, indent);
    } else if (typeof v == "boolean") {
      print_indented(k + ": " + v, indent);
    } else {
      print_indented(k + ": " + v.constructor.name, indent);
      do_dehydra_dump(v, indent + 1, depth - 1);
    }
  }
}

/**
 * Print string 's' indented by 'indent' spaces.
 */
function print_indented(s, indent) {
  for (let i = 0; i < indent; ++i) {
    s = "  " + s;
  }
  print(s);
}

/**
 * Simpler API for dehydra dumping. See do_dehydra_dump.
 */
function dehydra_dump(o) {
  print(typeof o);
  do_dehydra_dump(o, 1, 3);
}




// Cycle-collection common functions


//
// Analyzing which classes are cycle collected
//


// Array of classes with cycle collector participant inner classes.
let cctypes = [];

function is_cc(t) {
  if (cctypes.some(function (u) u === t))
    return true;
  return false;
}


function is_cc_inner_class_base(t) {
  return t.name === 'nsXPCOMCycleCollectionParticipant' ||
         t.name === 'nsCycleCollectionParticipant' ||
         t.name === 'nsScriptObjectTracer';
}


// I'm assuming cycle collection inner classes have only a single super class
function is_cc_inner_class_parent (t) {
  if (t.name === undefined)
    return false;
  if (t.typedef !== undefined)
    return interesting_type(t.typedef);
  if (is_cc_inner_class_base(t))
    return true;
  if (t.bases === undefined || t.bases.length !== 1)
    return false;
  return is_cc_inner_class_parent(t.bases[0].type);
}


// I'm assuming cycle collection inner classes have only a single super class
function is_cc_inner_class(t) {
  if (is_cc_inner_class_base(t)) {
    return false;
  }
  if (t.bases === undefined || t.bases.length !== 1) {
    return false;
  }
  return is_cc_inner_class_parent(t.bases[0].type);
}


// store nsiContentCache here if we find it
let nsiContentCache = undefined;

let nsiContentCacheEmptyExn = "Internal error: nsiContentCache is undefined.";


/* Dig around in nsAttrChildArray for nsIContent.  This is really
 * fragile.
 *
 * Should this somehow also return nsAttrValue?
 */
function nsAttrAndChildArray_contains(t) {
  for each (let m in t.members) {
    if (!m.isFunction)
      continue;
    if (m.name !== "nsAttrAndChildArray::ChildAt(PRUint32) const")
      continue;
    if (m.type.type.type === undefined)
      throw "nsAttrAndChildArray_contains was going to return undefined";
    return m.type.type.type;
  }
  throw "nsAttrAndChildArray_contains didn't find ChildAt";
}


/*
 * Return the type referred to via a reference counted container, or
 * undefined if there is none.
 */
function ptr_type_contains_help(t) {
  if (t.typedef) {
    return ptr_type_contains_help(t.typedef);
  }
  //if (t.variantOf) {
  //  return ptr_type_contains_help(t.variantOf);
  //}
  if (t.isArray) {
    return ptr_type_contains_help(t.type);
  }
  let temp = t.template;
  if (temp === undefined) {
    if (t.name === "nsAttrAndChildArray")
      return nsAttrAndChildArray_contains(t);
    return undefined;
  }

  if (temp.name === 'nsRefPtr' ||
      temp.name === 'nsCOMPtr' ||
      temp.name === 'nsCOMArray' ||
      temp.name === 'nsISupportsHashKey' ||
      temp.name === 'nsHashableHashKey' ||
      temp.name === 'nsCOMPtrHashKey') { // this is some kind of one-off wrapper class
    let t = ptr_type_contains_help(temp.arguments[0]);
    if (t !== undefined)
      return t;
    return temp.arguments[0];
  }
  if (temp.name === 'nsRunnableMethod') {
    if (temp.arguments.length !== 1) {
      if (temp.arguments.length !== 3)
	throw Error ("Unknown number of arguments to nsRunnableMethod.");
      if (temp.arguments[2] === 'false') {
	return undefined;
      }
      if (temp.arguments[2] !== 'true') {
	throw Error ("Unknown third argument to nsRunnableMethod.");
      }
    }
    return temp.arguments[0];
  }
  if (temp.name === 'nsRefPtrHashtable' ||
      temp.name === 'nsInterfaceHashtable') {
    return temp.arguments[1];
  }
  // this is a bit magical looking
  if (temp.name === 'nsAutoPtr' &&
      temp.arguments[0].name === 'nsBidiPresUtils') {
    // Should dig around in nsBidiPresUtils to get nsIContent, instead of caching.
    // Then get rid of the exception and any users of it.
    if (nsiContentCache)
      return nsiContentCache;
    throw nsiContentCacheEmptyExn;
  }
  if (temp.name === 'nsTArray' ||
      temp.name === 'nsTHashtable') {
    return ptr_type_contains_help(temp.arguments[0]);
  }
  return undefined;
}


function ptr_type_contains(t) {
  let i = ptr_type_contains_help(t);
  if (i === undefined)
    return undefined;
  // weak references don't need to be tracked by the cycle collector
  if (i.name === "nsIWeakReference")
    return undefined;
  return i;
}


/*
 * Classes we manually declare are not cycle collected.  Ideally, we
 * would check that this actually holds, and maybe get this
 * information directly from annotations on the files.
 *
 * This is basically supposed to be something like "classes with no
 * subclasses that are NS_DECL_CYCLE_COLLECTING_ISUPPORTS".
 */
let non_cc_class_whitelist =
  {
    // some basic non-cycle collected classes
    "nsCycleCollectingAutoRefCnt" : true,
    "nsAutoRefCnt" : true,
    "nsCString" : true,
    "nsString" : true,
    "nsWeakPtr" : true,
    // interfaces that seem to not have any CCed implementations
    "nsIURI" : true,
    "nsIDocShell" : true,
    "nsITimer" : true,
    "nsIDOMFileError" : true,
    "nsICharsetConverterManager" : true,
    "nsIDocumentEncoderNodeFixup" : true,
    "nsIContentSerializer" : true,
       // Some subclasses of this have nsRefPtrs to Elements and some
       // other suspicious looking things, but the subclasses
       // themselves are not CCed.
    "nsIOutputStream" : true,
    "nsIUnicodeEncoder" : true,
    "nsIAtom" : true,
    "nsIPrincipal" : true,
    "nsIChannel" : true, // I didn't look at all of these, but the
			 // ones I looked at were not cycle collected.
    "nsIDOMBlob" : true, // looks okay to me...
    "nsIRunnable" : true, // checked a bunch, none I saw were CCed
    "nsIStructuredCloneContainer" : true,
    "nsIApplicationCache" : true, // only one implementation, non-CCed.
    "nsIDOMFile" : true,
    "imgIRequest" : true,
    // individual classes that aren't cycle collected
    "mozilla::css::Loader" : true,
    "nsHTMLStyleSheet" : true,
    "nsDOMStyleSheetSetList" : true,
    "nsXMLEventsManager" : true,
    "nsAnonDivObserver" : true,
    "SelectionState" : true,
    "nsDOMValidityState" : true,
    "nsDOMFileList" : true,
  }


let no_unlink_whitelist =
  {
    "nsINodeInfo" : true, // These are intentionally not unlinked in
			  // order to keep alive ownerdocument until
			  // the node dies.  There's a special case in
			  // nsNodeInfoManager to ensure the document
			  // doesn't keep itself alive.
  }

/**
 * Return true if the given dehydra type object represents an XPCOM
 * pointer container type of interest to cycle collection.  Return
 * false if we're sure this is not a CC type, and undefined if we're
 * not sure.
 *
 * Should probably rename this.
 */
function is_ptr_type(t, isUnlink) {
  if (t.precision || t.min || t.bitfieldOf)
    return false;
  try
    {
      if (t.name === undefined)
	return undefined;
      if (non_cc_class_whitelist[t.name])
	return false;
      let tc = ptr_type_contains(t);
      if (tc === undefined)
	return undefined;
      if (non_cc_class_whitelist[tc.name] ||
	  (isUnlink && no_unlink_whitelist[tc.name])) {
	return false;
      }
      return true;
    }
  catch (err)
    {
      if (err === nsiContentCacheEmptyExn)
	return true;
      throw err;
    }
}


function type_name_string(t) {
  if (t.isPointer) {
    return type_name_string(t.type) + "*";
  }
  if (t.isReference) {
    return type_name_string(t.type) + "&";
  }
  return t.name;
}


function find_pointer_print (m) {
  if (DEBUG_PRINT) {
    // Filter out a few common weird failure cases.  Probably dumb to
    // have it here, but oh well, good enough for now.
    let t = m.type;
    let temp = t.template;
    if (temp) {
      if (temp.name === 'nsAutoPtr' &&
	  is_ptr_type(temp.arguments[0]) === false)
	return;
      if (temp.name === 'nsDataHashtable' &&
	  is_ptr_type(temp.arguments[1]) === false)
	return;
    }
    debug_print("    -- " + type_name_string(t));
  }
}

/**
 * Generate dehydra member objects for all the member fields
 * of a dehydra type that are cycle-collection-related pointer types.
 * See also is_ptr_type.
 */
function find_ptrs(type, isUnlink) {
  for each (let m in type.members) {
    if (m.isFunction)
      continue;
    let ipt = is_ptr_type(m.type, isUnlink);
    if (ipt)
      yield m;
    else if (ipt === undefined)
      find_pointer_print(m);
  }
  for each (let {type:b} in type.bases)
    for (let t in find_ptrs(b, isUnlink))
      yield t
}


/**
 * Return true if the given dehydra type is a C++ abstract base class.
 */
function is_abstract(t) {
  if (t.members === undefined) {
    throw Error ("Expected class " + t.name + " to have members.");
  }
  return t.members.some(function (m) m.isVirtual == 'pure');
}


