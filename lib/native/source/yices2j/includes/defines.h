// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

#include <stdlib.h>
#include <jni.h>
#include <gmp.h>
#include "yices.h"


#define CHECK_FOR_NULL(var) \
  if (var == NULL) { \
    return 0; \
  }

typedef void jvoid; // for symmetry to jint, jlong etc.

// Macros for defining JNI functions which call Yices
// Use them as follows:
//
// DEFINE_FUNC(java_return_type, escaped_name_without_yices) WITH_X_ARGS(java_arg_types)
// for each arg a definition like TERM_ARG(position)
// CALLX(yices_return_type, function_name_without_yices)
// return definition like TERM_RETURN depending on the return type


#define DEFINE_FUNC(jreturn, func_escaped) \
  JNIEXPORT j##jreturn JNICALL Java_org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi_yices_##func_escaped

#define WITHOUT_ARGS \
  (JNIEnv *jenv, jclass jcls) {

#define WITH_ONE_ARG(jtype) \
  (JNIEnv *jenv, jclass jcls, j##jtype arg1) {

#define WITH_TWO_ARGS(jtype1, jtype2) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2) {

#define WITH_THREE_ARGS(jtype1, jtype2, jtype3) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3) {

#define WITH_FOUR_ARGS(jtype1, jtype2, jtype3, jtype4) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4) {

#define WITH_FIVE_ARGS(jtype1, jtype2, jtype3, jtype4, jtype5) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4, j##jtype5 arg5) {

#define WITH_SIX_ARGS(jtype1, jtype2, jtype3, jtype4, jtype5, jtype6) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4, j##jtype5 arg5, j##jtype6 arg6) {

#define WITH_SEVEN_ARGS(jtype1, jtype2, jtype3, jtype4, jtype5, jtype6, jtype7) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4, j##jtype5 arg5, j##jtype6 arg6, j##jtype7 arg7) {

#define SIMPLE_ARG(mtype, num) \
  mtype m_arg##num = arg##num;

#define UINT32_ARG(num) SIMPLE_ARG(uint32_t, num)

#define NULL_ARG(mtype, num) \
		mtype *m_arg##num = NULL;

#define STRING_ARG(num) \
  char * m_arg##num = (char *)(*jenv)->GetStringUTFChars(jenv, arg##num, NULL); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

//may cause memory problems
#define INT_ARRAY_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *)((*jenv)->GetIntArrayElements(jenv, arg##num, NULL)); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

#define EMPTY_INT_ARRAY_ARG(mtype, num) \
  mtype *m_arg##num;\
  size_t sz = (size_t)(arg##num); \
  m_arg##num = (mtype *)malloc(sizeof(mtype) * sz); \
  if (m_arg##num == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for calling Yices"); \
  } \

#define EMPTY_YVAL_ARRAY_ARG(num) \
  yval_t *m_arg##num;\
  size_t sz = (size_t)(arg##num); \
  m_arg##num = (yval_t *)malloc(sizeof(yval_t) * sz); \
  if (m_arg##num == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for calling Yices"); \
  } \

//may cause memory problems
#define LONG_ARRAY_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *)((*jenv)->GetLongArrayElements(jenv, arg##num, NULL)); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

#define POINTER_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *) arg##num;

//For ** types
#define POINTER_POINTER_ARG(mtype, num) \
  mtype ** m_arg##num = (mtype **) arg##num;

#define INT_POINTER_ARG(num) \
  int32_t s_arg##num = 0; \
  int32_t *m_arg##num = &s_arg##num;

#define LONG_POINTER_ARG(num) \
  int64_t s_arg##num = 0; \
  int64_t *m_arg##num = &s_arg##num;

#define DOUBLE_POINTER_ARG(num) \
  double s_arg##num = 0; \
  double *m_arg##num = &s_arg##num;

#define TERM_VECTOR_ARG(num) \
  term_vector_t s_arg##num; \
  term_vector_t *m_arg##num = &s_arg##num; \
  yices_init_term_vector(m_arg##num); \

#define TYPE_VECTOR_ARG(num) \
  type_vector_t s_arg##num; \
  type_vector_t *m_arg##num = &s_arg##num; \
  yices_init_type_vector(m_arg##num); \

#define YVAL_VECTOR_ARG(num) \
  yval_vector_t s_arg##num; \
  yval_vector_t *m_arg##num = &s_arg##num; \
  yices_init_yval_vector(m_arg##num); \

#define EMPTY_YVAL_ARG(num) \
  yval_t s_arg##num; \
  yval_t *m_arg##num = &s_arg##num; \

/*
 * Builds an yval_t from java input where
 * num = Position of the yval_t in the c function call
 * id = Position of the Java arg to use as node_id
 * tag = Position of the Java arg to use as node_tag
*/
#define YVAL_ARG(num, id, tag) \
  yval_t s_arg##num; \
  yval_t *m_arg##num = &s_arg##num; \
  if(arg##id < 0) { \
    throwException(jenv, "java/lang/IllegalArgumentException", "An yval_id cannot be negative."); \
  }\
  if(arg##tag < 0 || arg##tag > 8) { \
    throwException(jenv, "java/lang/IllegalArgumentException", "Yval_tag is negative or not a valid yval_tag."); \
  } \
  m_arg##num->node_id = arg##id; \
  m_arg##num->node_tag = arg##tag; \

#define MPQ_ARG(num) \
  mpq_t m_arg##num; \
  mpq_init(m_arg##num); \

#define CALL0(mreturn, func) mreturn retval = yices_##func();
#define CALL1(mreturn, func) mreturn retval = yices_##func(m_arg1);
#define CALL2(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2);
#define CALL3(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3);
#define CALL4(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4);
#define CALL5(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4, m_arg5);
#define CALL6(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4, m_arg5, m_arg6);
#define CALL7(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4, m_arg5, m_arg6, m_arg7);
#define VOID_CALL0(func) yices_##func(); }
#define VOID_CALL1(func) yices_##func(m_arg1); }
#define VOID_CALL2(func) yices_##func(m_arg1, m_arg2); }
#define VOID_CALL2_WITH_RETURN(func) yices_##func(m_arg1, m_arg2);

#define FREE_STRING_OPTIONAL_ARG(num) \
  if(arg##num != NULL) {(*jenv)->ReleaseStringUTFChars(jenv, arg##num, m_arg##num); } \
  out##num:

#define FREE_STRING_ARG(num) \
  (*jenv)->ReleaseStringUTFChars(jenv, arg##num, m_arg##num); \
  out##num:

#define FREE_INT_ARRAY_ARG(num) \
  (*jenv)->ReleaseIntArrayElements(jenv, arg##num, m_arg##num, 0); \
  out##num:

#define FREE_LONG_ARRAY_ARG(num) \
  (*jenv)->ReleaseLongArrayElements(jenv, arg##num, m_arg##num, 0); \
  out##num:

#define INT_INIT \
  int retval = -1;

#define TERM_VECTOR_ARG_INIT INT_INIT

#define POINTER_INIT(type) \
  type* retval = NULL;

//may cause memory leak through yices_error_string
#define INT_RETURN \
  if (retval <= 0 && yices_error_code() != 0){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jint)retval; \
}

#define PLAIN_STRING_RETURN \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, retval); \
  } \
  yices_free_string(retval); \
  return jretval; \
}

#define STRING_RETURN \
  if (retval == NULL && yices_error_code()!=0) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return NULL; \
  } \
  PLAIN_STRING_RETURN

#define CONST_STRING_RETURN \
   if (retval == NULL && yices_error_code()!=0) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return NULL; \
  } \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, retval); \
  } \
  return jretval; \
}

//may cause memory leak through yices_error_string
#define POINTER_RETURN \
  if(retval == NULL){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return 0; \
  } \
  return (long) retval; \
}

#define POINTER_ARG_RETURN(num) \
  if(retval == -1 && yices_error_code != 0){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return 0; \
  } \
  if(m_arg##num == NULL){ \
    throwException(jenv, "java/lang/IllegalArgumentException", "Pointer to return was NULL"); \
    return 0; \
  } \
  return (long) m_arg##num; \
}
//may cause memory leak through yices_error_string
#define FROM_INT_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jint) *m_arg##num; \
 }

//may cause memory leak through yices_error_string
#define FROM_LONG_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jlong) *m_arg##num; \
 }

#define FROM_DOUBLE_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jdouble) *m_arg##num; \
 }

#define MPQ_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
  } \
  char * mpqValue = mpq_get_str(NULL, 10, m_arg##num); \
  if(mpqValue == NULL){ \
    throwException(jenv, "java/lang/NullPointerException", "Result of mpq_get_str was NULL."); \
  } \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, mpqValue); \
  } \
  mpq_clear(m_arg##num); \
  free(mpqValue); \
  return jretval; \
}

#define YVAL_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
  } \
  int yval[2]; \
  yval[0] = s_arg##num.node_id; \
  yval[1] = s_arg##num.node_tag; \
  jintArray jretval = 0; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewIntArray(jenv, 2); \
    if(jretval != NULL){ \
      (*jenv)->SetIntArrayRegion(jenv, jretval, 0, 2, yval); \
    } \
  } \
  return jretval; \
}

#define INT_ARRAY_RETURN(num) \
  jintArray jretval = NULL; \
  if(retval == -1){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    goto out; \
  } \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewIntArray(jenv, sz); \
    if(jretval != NULL){ \
      (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, m_arg##num); \
    } \
  } \
  out: \
  free(m_arg##num);\
  return jretval; \
}

#define TERM_VECTOR_ARG_RETURN(num) \
  jintArray jretval = NULL; \
  if ((*jenv)->ExceptionCheck(jenv)) { \
    goto out; \
  } \
  if(retval == -1){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    goto out; \
  } \
  size_t sz = s_arg##num.size; \
  jint *jarr = malloc(sizeof(jint) * sz); \
  if (jarr == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Yices"); \
    goto out; \
  } \
  size_t i; \
  term_t * data = s_arg##num.data; \
  for (i = 0; i < sz; ++i) { \
      jarr[i] = (jint)((size_t)data[i]); \
  } \
  jretval = (*jenv)->NewIntArray(jenv, sz); \
  if (jretval != NULL) { \
    (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, jarr); \
  } \
  free(jarr); \
  \
  out: \
  yices_delete_term_vector(m_arg##num); \
  return jretval; \
}

#define TYPE_VECTOR_ARG_RETURN(num) \
  jintArray jretval = NULL; \
  if ((*jenv)->ExceptionCheck(jenv)) { \
    goto out; \
  } \
  if(retval == -1){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return jretval; \
    goto out; \
  } \
  size_t sz = s_arg##num.size; \
  jint *jarr = malloc(sizeof(jint) * sz); \
  if (jarr == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Yices"); \
    goto out; \
  } \
  size_t i; \
  term_t * data = s_arg##num.data; \
  for (i = 0; i < sz; ++i) { \
      jarr[i] = (jint)((size_t)data[i]); \
  } \
  jretval = (*jenv)->NewIntArray(jenv, sz); \
  if (jretval != NULL) { \
    (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, jarr); \
  } \
  free(jarr); \
  \
  out: \
  yices_delete_type_vector(m_arg##num); \
  return jretval; \
}


// Define aliases for Yices types
typedef jlong jjctx;
#define CTX_ARG(num) POINTER_ARG(context_t, num)
#define CTX_ARG_VOID(num) POINTER_ARG(context_t, num)
#define CTX_RETURN POINTER_RETURN

typedef jlong jjconf;
#define CONF_ARG(num) POINTER_ARG(ctx_config_t, num)
#define CONF_ARG_VOID(num) POINTER_ARG(ctx_config_t, num)
#define CONF_RETURN POINTER_RETURN

typedef jlong jjparam;
#define PARAM_ARG(num) POINTER_ARG(param_t, num)
#define PARAM_ARG_VOID(num) POINTER_ARG(param_t, num)
#define PARAM_RETURN POINTER_RETURN

typedef jint jjterm;
#define TERM_ARG(num) SIMPLE_ARG(term_t, num)
#define TERM_ARG_VOID(num) SIMPLE_ARG(term_t, num)
#define TERM_INIT INT_INIT
#define TERM_RETURN INT_RETURN

typedef jlong jjmodel;
#define MODEL_ARG(num) POINTER_ARG(model_t, num)
#define MODEL_ARG_VOID(num) POINTER_ARG(model_t, num)
#define MODEL_INIT POINTER_INIT(model_t)
#define MODEL_RETURN POINTER_RETURN
//For things like model_t **
#define MODEL_ARG_POINTER(num) POINTER_POINTER_ARG(model_t, num)


typedef jintArray jjtermArray;
#define TERM_ARRAY_ARG(num) INT_ARRAY_ARG(term_t, num)
#define FREE_TERM_ARRAY_ARG(num) FREE_INT_ARRAY_ARG(num)

typedef jint jjtype;
#define TYPE_ARG(num) SIMPLE_ARG(type_t, num)
#define TYPE_INIT INT_INIT
#define TYPE_RETURN INT_RETURN

typedef jintArray jjtypeArray;
#define TYPE_ARRAY_ARG(num) INT_ARRAY_ARG(type_t, num)
#define FREE_TYPE_ARRAY_ARG(num) FREE_INT_ARRAY_ARG(num)

typedef jint jjboolean;
#define BOOLEAN_RETURN INT_RETURN

typedef jlong jjyval;
typedef jint jjnodeid;
typedef jint jjnodetag;

// Abbreviations for common combinations of return and argument types

#define get_yices_type(name) \
  DEFINE_FUNC(jtype, 1##name##_1type) WITHOUT_ARGS \
  CALL0(type_t, ##name##_type) \
  TYPE_RETURN

#define yices_arith(name) \
  DEFINE_FUNC(jterm, 1arith_1##name##_1atom) WITH_ONE_ARG(jterm) \
  TERM_ARG(1) \
  CALL1(term_t, arith_##name##_atom) \
  TERM_RETURN

#define yices_arith2(name) \
  DEFINE_FUNC(jterm, 1arith_1##name##_1atom) WITH_TWO_ARGS(jterm, jterm) \
  TERM_ARG(1) \
  TERM_ARG(2) \
  CALL2(term_t, arith_##name##_atom) \
  TERM_RETURN

#define yices_type_is(name) \
  DEFINE_FUNC(jboolean, 1type_1is_1##name) WITH_ONE_ARG(jtype) \
  TYPE_ARG(1) \
  CALL1(type_t, type_is_##name) \
  BOOLEAN_RETURN

#define yices_term_is(name) \
  DEFINE_FUNC(jboolean, 1term_1is_1##name) WITH_ONE_ARG(jterm) \
  TERM_ARG(1) \
  CALL1(type_t, term_is_##name) \
  BOOLEAN_RETURN

