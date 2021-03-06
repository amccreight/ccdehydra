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
// These are discovered during analysis and added here.
let cctypes = [];

// Return true if this is a previously discovered CCed class.
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


function is_nsISupports(t)
{
  let name = t.name;
  if (name === undefined)
    return false;
  if (t.typedef !== undefined)
    return is_nsISupports(t.typedef);
  if (name === 'nsISupports')
    return true;

  for each (let {type:base} in t.bases) {
    if (base.name === undefined) {
      throw Error("Nameless type on a subcall.");
    }
    if (is_nsISupports(base))
      return true;
  }

  return false;
}


// I'm assuming cycle collection inner classes have only a single super class
function is_cc_inner_class_parent (t) {
  if (t.name === undefined)
    return false;
  if (t.typedef !== undefined)
    return is_nsISupports(t.typedef);
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
 * Could memoize the result.
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
    "nsCycleCollectingAutoRefCnt" : "peterv",
    "nsAutoRefCnt" : "peterv",
    "nsCString"    : "peterv",
    "nsString"     : "peterv",
    "nsWeakPtr"    : "peterv",

    // individual classes that aren't cycle collected
    "nsDOMStyleSheetSetList" : "peterv", // with new DOM bindings, needs Traverse
    "mozilla::css::Loader"   : "mccr8",
    "nsHTMLStyleSheet"       : "mccr8",
    "nsXMLEventsManager"     : "mccr8",
    "nsAnonDivObserver"      : "mccr8",
    "SelectionState"         : "mccr8",
    "nsDOMValidityState"     : "mccr8",
    "nsDOMSettableTokenList" : true,
    "nsSelectState"          : true,

    // interfaces that seem to not have any CCed implementations
    "nsIDocShell"                 : "smaug",
    "nsITimer"                    : "smaug",
    "nsIDOMFileError"             : "smaug",
    "nsICharsetConverterManager"  : "smaug",
    "nsIContentSerializer"        : "smaug",
    "nsIAtom"                     : "smaug",
    "nsIStructuredCloneContainer" : "smaug",
    "nsIOutputStream"     : "bz",
    "nsIUnicodeEncoder"   : "bz",
    "nsIRequest"          : "bz",
    "nsIChannel"          : "bz",
    "nsIApplicationCache" : "bz",
    "nsIDOMBlob" : "khuey",

    "nsIDOMFile" : "smaug", // might be needed in the future
    "nsDOMFileList" : "smaug", // might be needed in the future
  }


let no_unlink_whitelist =
  {
    "nsINodeInfo" : true, // These are intentionally not unlinked in
			  // order to keep alive ownerdocument until
			  // the node dies.  There's a special case in
			  // nsNodeInfoManager to ensure the document
			  // doesn't keep itself alive.
  }


/*

FEEDBACK

sicking:
  nsIInterfaceRequestor
  nsIAsyncVerifyRedirectCallback

  These are only briefly non-null in content/base/src/nsXMLHttpRequest,
  but sicking says that we should Traverse, but not Unlink them, because
  it won't be much problem.  Add to no_unlink_whitelist.

bz:
  nsIURI, nsIPrincipal: probably should be cycle collected, though mostly 
    they are leaves.
  imgIRequest: should be CCed

  nsIRequest, nsIChannel: "These are generally not main-thread-only, sort of.
    Worth checking with the necko folks."

  nsIRunnable: "These are often used to post events
    cross-thread.... though sometimes they can be same-thread too.  CC
    should probably happen on a case by case basis."

peterv:

  nsIObserver: Is it okay to skip this?  "Normally it isn't, since
    these fields could hold a nsGlobalWindow, right? It might be that
    we've determined that they never hold a nsGlobalWindow, but that's
    usually hard to enforce. On the other hand, there are probably a
    lot of nsIObserver implementations so this might end up adding CC
    to a ton of other classes."

smaug:

  nsIDocumentEncoderNodeFixup: "In theory extensions could implement
    nsIDocumentEncoderNodeFixup and use with DocumentEncoder.
    DocumentEncoder should traverse/unlink mNodeFixup because of that.
    The in-tree implementation should be safe."

  nsIDocShell: "I wouldn't bother [traversing or unlinking] right
    now. Docshell shouldn't really create cycles atm, since docshells
    create a tree, where parent owns children.  The tree is also
    manually destroyed in the needed places.  There has been few leaks
    related to this, but in no cases would traversing/unlinking have
    helped, IIRC.

    jst: "Uh, nsIDocShell is still used on other threads than the main
    thread, so we can't properly cycle collect it even though we'd
    really want to.  There's bugs, and I think Brian Smith is actively
    working on removing the remaining off-main-thread usages here, so
    some day we might be able to. I have a vague memory of hearing
    some people still traversing nsIDocShell members in preparation
    for when we actually cycle collect them, but I'm short on
    specifics on this topic.

  nsIDOMFile, nsDOMFileList: "As of now traversing/unlinking those
    isn't needed.  I added them because of
    https://bugzilla.mozilla.org/show_bug.cgi?id=664467#c1 "

 */


/* This function is sketchy: it relies on process_type saving away
 * classes that are found to be cycle collected, and that we always
 * determine accurately if t is cycle collected by the time we run
 * this.
 */
function concrete_cc_class (t) {
  return (!is_abstract(t) && t.is_incomplete === false && is_cc(t));
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
	  //concrete_cc_class(t) ||   hmm I am not sure what to think of this
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


// is_ptr_type doesn't handle a few common nested cases correctly
function ptr_actually_ok (t) {
  let temp = t.template;
  if (temp) {
    if (temp.name === 'nsAutoPtr' &&
	is_ptr_type(temp.arguments[0]) === false)
      return true;
    if (temp.name === 'nsDataHashtable' &&
	is_ptr_type(temp.arguments[1]) === false)
      return true;
  }
  return false;
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
      yield {field : m, certain:true};
    else if (ipt === undefined && !ptr_actually_ok(m.type)) {
      yield {field : m, certain:false};
    }
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


