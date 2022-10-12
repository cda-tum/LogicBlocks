/* -*- C -*-
 * 
 * MathSAT5 is copyrighted 2009-2021 by Fondazione Bruno Kessler, Trento, Italy,
 * University of Trento, Italy, and others. All rights reserved.
 * 
 * MathSAT5 is available for research and evaluation purposes only.
 * It can not be used in a commercial environment, particularly as part of a
 * commercial product, without written permission. MathSAT5 is provided as is,
 * without any warranty.
 * 
 * Please write to mathsat@fbk.eu for additional questions regarding licensing
 * MathSAT5 or obtaining more up-to-date versions.
 *
 * C API for the MathSAT 5 solver
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of MathSAT 5.
 */

/**
 * \file mathsat.h
 *
 * \brief API for the MathSAT SMT solver.
 */

#ifndef MSAT_MATHSAT_H_INCLUDED
#define MSAT_MATHSAT_H_INCLUDED

#include <stdio.h>
#include <stddef.h>
#include <gmp.h>

#include <inttypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \name Data types and special values
 */

/*@{*/

/**
 * \brief MathSAT configuration.
 */
typedef struct msat_config { void *repr; } msat_config;

/**
 * \brief MathSAT environment.
 */
typedef struct msat_env { void *repr; } msat_env;

/**
 * \brief MathSAT term.
 *
 * A term is a constant, a number, an atom, or an arbitrary boolean
 * combination of those. It is the basic block of MathSAT abstract syntax
 * trees.
 */
typedef struct msat_term { void *repr; } msat_term;

/**
 * \brief MathSAT declaration.
 *
 * Declaration of constants and uninterpreted functions/predicates.
 */
typedef struct msat_decl { void *repr; } msat_decl;

/**
 * \brief MathSAT data types.
 */
typedef struct msat_type { void *repr; } msat_type;

/**
 * MathSAT result.
 */ 
typedef enum {
    MSAT_UNKNOWN = -1, /**< Unknown. */
    MSAT_UNSAT,        /**< Unsatisfiable. */
    MSAT_SAT           /**< Satisfiable. */
} msat_result;

/**
 * MathSAT truth value.
 */
typedef enum {
    MSAT_UNDEF = -1,  /**< Undefined/unknown. */
    MSAT_FALSE,       /**< False. */
    MSAT_TRUE         /**< True. */
} msat_truth_value;


/**
 * MathSAT symbol tag.
 */
typedef enum {
    MSAT_TAG_ERROR = -1,
    MSAT_TAG_UNKNOWN = 0,
    MSAT_TAG_TRUE,          /**< the Boolean constant True */
    MSAT_TAG_FALSE,         /**< the Boolean constant False */
    MSAT_TAG_AND,           /**< the AND Boolean connective */
    MSAT_TAG_OR,            /**< the OR Boolean connective */
    MSAT_TAG_NOT,           /**< the NOT Boolean connective */
    MSAT_TAG_IFF,           /**< the IFF Boolean connective */
    MSAT_TAG_PLUS,          /**< arithmetic addition */
    MSAT_TAG_TIMES,         /**< arithmetic multiplication */
    MSAT_TAG_DIVIDE,        /**< arithmetic division */
    MSAT_TAG_FLOOR,         /**< floor function */
    MSAT_TAG_LEQ,           /**< arithmetic <= */
    MSAT_TAG_EQ,            /**< equality */
    MSAT_TAG_ITE,           /**< term-level if-then-else */
    MSAT_TAG_INT_MOD_CONGR, /**< integer modular congruence */
    MSAT_TAG_BV_CONCAT,     /**< BV concatenation */
    MSAT_TAG_BV_EXTRACT,    /**< BV selection */
    MSAT_TAG_BV_NOT,        /**< BV bitwise not */
    MSAT_TAG_BV_AND,        /**< BV bitwise and */
    MSAT_TAG_BV_OR,         /**< BV bitwise or */
    MSAT_TAG_BV_XOR,        /**< BV bitwise xor */
    MSAT_TAG_BV_ULT,        /**< BV unsigned < */
    MSAT_TAG_BV_SLT,        /**< BV signed < */
    MSAT_TAG_BV_ULE,        /**< BV unsigned <= */
    MSAT_TAG_BV_SLE,        /**< BV signed < */
    MSAT_TAG_BV_COMP,       /**< BV bit comparison */
    MSAT_TAG_BV_NEG,        /**< BV unary minus */
    MSAT_TAG_BV_ADD,        /**< BV addition */
    MSAT_TAG_BV_SUB,        /**< BV subtraction */
    MSAT_TAG_BV_MUL,        /**< BV multiplication */
    MSAT_TAG_BV_UDIV,       /**< BV unsigned division */
    MSAT_TAG_BV_SDIV,       /**< BV signed division */
    MSAT_TAG_BV_UREM,       /**< BV unsigned remainder */
    MSAT_TAG_BV_SREM,       /**< BV signed remainder */
    MSAT_TAG_BV_LSHL,       /**< BV logical left shift */
    MSAT_TAG_BV_LSHR,       /**< BV logical right shift */
    MSAT_TAG_BV_ASHR,       /**< BV arithmetic right shift */
    MSAT_TAG_BV_ROL,        /**< BV rotate left */
    MSAT_TAG_BV_ROR,        /**< BV rotate right */
    MSAT_TAG_BV_ZEXT,       /**< BV zero extension */
    MSAT_TAG_BV_SEXT,       /**< BV sign extension */
    MSAT_TAG_ARRAY_READ,    /**< Array read/select operation */
    MSAT_TAG_ARRAY_WRITE,   /**< Array write/store operation */
    MSAT_TAG_ARRAY_CONST,   /**< Constant arrays */
    MSAT_TAG_FP_EQ,         /**< FP IEEE equality */
    MSAT_TAG_FP_LT,         /**< FP < */
    MSAT_TAG_FP_LE,         /**< FP <= */
    MSAT_TAG_FP_NEG,        /**< FP unary minus */
    MSAT_TAG_FP_ADD,        /**< FP addition */
    MSAT_TAG_FP_SUB,        /**< FP subtraction */
    MSAT_TAG_FP_MUL,        /**< FP multiplication */
    MSAT_TAG_FP_DIV,        /**< FP division */
    MSAT_TAG_FP_SQRT,       /**< FP square root */
    MSAT_TAG_FP_ABS,        /**< FP absolute value */
    MSAT_TAG_FP_MIN,        /**< FP min */
    MSAT_TAG_FP_MAX,        /**< FP max */
    MSAT_TAG_FP_CAST,       /**< FP format conversion */
    MSAT_TAG_FP_ROUND_TO_INT,/**< FP round to integer */
    MSAT_TAG_FP_FROM_SBV,   /**< FP conversion from a signed BV */
    MSAT_TAG_FP_FROM_UBV,   /**< FP conversion from an unsigned BV */
    MSAT_TAG_FP_TO_SBV,     /**< FP conversion to signed BV */
    MSAT_TAG_FP_TO_UBV,     /**< FP conversion to unsigned BV */
    MSAT_TAG_FP_AS_IEEEBV,  /**< FP as IEEE BV (access to the bits) */
    MSAT_TAG_FP_ISNAN,      /**< FP check for NaN */
    MSAT_TAG_FP_ISINF,      /**< FP check for infinity */
    MSAT_TAG_FP_ISZERO,     /**< FP check for zero */
    MSAT_TAG_FP_ISSUBNORMAL,/**< FP check for subnormal */
    MSAT_TAG_FP_ISNORMAL,   /**< FP check for normal */
    MSAT_TAG_FP_ISNEG,      /**< FP check for negative */
    MSAT_TAG_FP_ISPOS,      /**< FP check for positive */
    MSAT_TAG_FP_FROM_IEEEBV,/**< FP conversion from IEEE BV */
    MSAT_TAG_INT_FROM_UBV,  /**< Unsigned BV -> INT conversion */
    MSAT_TAG_INT_FROM_SBV,  /**< Signed BV -> INT conversion */
    MSAT_TAG_INT_TO_BV,     /**< INT -> BV conversion */
    MSAT_TAG_PI,            /**< Pi constant */
    MSAT_TAG_EXP,           /**< Exponential function */
    MSAT_TAG_SIN,           /**< Sine function */
    MSAT_TAG_LOG,           /**< Natural logarithm function */
    MSAT_TAG_POW,           /**< Power function */
    MSAT_TAG_ASIN,          /**< Arcsin function */
    MSAT_TAG_FORALL,        /**< Universal quantifier */
    MSAT_TAG_EXISTS         /**< Existential quantifier */
} msat_symbol_tag;

#define MSAT_TAG_FP_TO_BV MSAT_TAG_FP_TO_SBV

/**
 * \brief Callback function to be notified about models found by ::msat_all_sat
 *
 * This callback function can be used to be notified about the models found by
 * the AllSat algorithm. Such models contain the truth values of the important
 * atoms, as specified with ::msat_all_sat. Each term in the \a model array is
 * either an important atom or its negation, according to the truth value in
 * the model. Notice that the \a model array is read-only, and will be valid
 * only until the callback function returns.
 * If the function returns zero, then the current search is aborted
 */
typedef int (*msat_all_sat_model_callback)(msat_term *model, int size,
                                           void *user_data);

/**
 * \brief MathSAT model.
 *
 * A model object lets you evaluate terms under the solution found in the last
 * check. The functionality is similar to ::msat_get_model_value(), but a
 * model object can be queried even after having modified the assertion stack
 * of the environment. If the environment is a shared one, the model is valid
 * even after the environment has been destroyed (however, the "master"
 * environment must still be valid).
 */
typedef struct msat_model { void *repr; } msat_model;

/**
 * \brief MathSAT model iterator.
 *
 * An iterator object that lets you retrieve the value of constants and
 * uninterpreted function applications that make a formula evaluate to true.
 * Notice that sometimes MathSAT will not assign a model value to every
 * constant/function application in the formula: in this case, the missing
 * terms can be assigned any (legal) value.
 */ 
typedef struct msat_model_iterator { void *repr; } msat_model_iterator;


/**
 * \brief Callback function to be notified about models found by
 * ::msat_solve_diversify
 *
 * This callback function can be used to be notified about the models found by
 * the diversification algorithm. If the function returns non-zero, then the
 * current search is aborted
 */
typedef int (*msat_solve_diversify_model_callback)(msat_model_iterator it,
                                                   void *user_data);

/**
 * MathSAT status for the callback passed to ::msat_visit_term
 */
typedef enum {
    MSAT_VISIT_PROCESS = 0, /**< Continue visiting */
    MSAT_VISIT_SKIP = 1,    /**< Skip this term and the subterms */
    MSAT_VISIT_ABORT = 2    /**< Abort visit immediately */
} msat_visit_status;

/**
 * \brief Callback function to visit a term DAG with ::msat_visit_term
 *
 * This callback function gets called by the term visitor for each visited
 * subterm. The \a preorder flag tells whether the function is called before
 * or after visiting the subterms. The return value of this function
 * determines how the visit should continue (see ::msat_visit_status)
 */
typedef msat_visit_status (*msat_visit_term_callback)(msat_env e, msat_term t,
                                                      int preorder,
                                                      void *user_data);

/**
 * \brief Custom test for early termination of search
 *
 * See ::msat_set_termination_test
 */
typedef int (*msat_termination_test)(void *user_data);


/**
 * \brief Manager for proofs generated by MathSAT
 *
 * See ::msat_get_proof_manager
 */
typedef struct msat_proof_manager { void *repr; } msat_proof_manager;

/**
 * \brief Proof objects created by MathSAT
 *
 * See ::msat_get_proof
 */
typedef struct msat_proof { void *repr; } msat_proof;


/**
 * \brief External Boolean unsat core extraction function, to be used with
 *        ::msat_get_unsat_core_ext.
 *
 * The function accepts as input an array of integers representing the input
 * problem in DIMACS format (with different clauses separated by a 0) and an
 * array of group indices (positive integers, with index 0 reserved for the
 * "background" group), and it must modify the array of groups in-place for
 * storing the indices of the groups in the unsat core. The parameter \a
 * size_in_out gives the number of clauses in the input cnf, and should be
 * modified to store the number of groups in the computed core. The function
 * should return a non-zero value to signal an error.
 * See also http://www.satcompetition.org/2011/rules.pdf (MUS track)
 */
typedef int (*msat_ext_unsat_core_extractor)(int *cnf_in, int *groups_in_out,
                                             size_t *size_in_out,
                                             void *user_data);

#ifndef SWIG /* avoid exposing macros when wrapping with SWIG */

/**
 * \brief Error checking for configurations
 *
 * Use this macro to check whether returned values of type ::msat_config are
 * valid
 */
#define MSAT_ERROR_CONFIG(cfg) ((cfg).repr == NULL)

/**
 * \brief Error checking for environments
 *
 * Use this macro to check whether returned values of type ::msat_env are valid
 */
#define MSAT_ERROR_ENV(env) ((env).repr == NULL)

/**
 * \brief Error checking for terms
 *
 * Use this macro to check whether returned values of type ::msat_term are valid
 */
#define MSAT_ERROR_TERM(term) ((term).repr == NULL)

/**
 * \brief Sets given term to be an error term
 *
 * Use this macro to make terms error terms.
 */
#define MSAT_MAKE_ERROR_TERM(term) ((term).repr = NULL)

/**
 * \brief Error checking for declarations
 *
 * Use this macro to check whether returned values of type ::msat_decl are valid
 */
#define MSAT_ERROR_DECL(decl) ((decl).repr == NULL)

/**
 * \brief Error checking for data types
 *
 * Use this macro to check whether returned values of type ::msat_type are valid
 */
#define MSAT_ERROR_TYPE(tp) ((tp).repr == NULL)

/**
 * \brief Error checking for model iterators
 *
 * Use this macro to check whether returned values of type
 * ::msat_model_iterator are valid
 */
#define MSAT_ERROR_MODEL_ITERATOR(iter) ((iter).repr == NULL)

/**
 * \brief Error checking for models
 *
 * Use this macro to check whether returned values of type
 * ::msat_model are valid
 */
#define MSAT_ERROR_MODEL(model) ((model).repr == NULL)

/**
 * \brief Error checking for proof managers
 *
 * Use this macro to check whether returned values of type
 * ::msat_proof_manager are valid
 */
#define MSAT_ERROR_PROOF_MANAGER(mgr) ((mgr).repr == NULL)

/**
 * \brief Error checking for proofs
 *
 * Use this macro to check whether returned values of type
 * ::msat_proof are valid
 */
#define MSAT_ERROR_PROOF(p) ((p).repr == NULL)

/**
 * \brief Error checking for objectives
 *
 * Use this macro to check whether returned values of type ::msat_objective are valid
 */
#define MSAT_ERROR_OBJECTIVE(objective) ((objective).repr == NULL)

/**
 * \brief Error checking for objective iterators
 *
 * Use this macro to check whether returned values of type
 * ::msat_objective_iterator are valid
 */
#define MSAT_ERROR_OBJECTIVE_ITERATOR(iter) ((iter).repr == NULL)

#endif /* SWIG */


/**
 * \brief Function for deallocating the memory accessible by pointers returned
 *        by MathSAT
 */
void msat_free(void *ptr);

/**
 * \brief Gets the current MathSAT version.
 * \return A version string, with version information about MathSAT, the GMP
 *         library and the compiler used.
 *         The string must be deallocated by the user with ::msat_free().
 */ 
char *msat_get_version(void);

/**
 * \brief Retrieves the last error message generated while operating in the
 *        given enviroment.
 *
 * \param env The environment in which the error occurred.
 * \return A pointer to the last error message generated.
 */
const char *msat_last_error_message(msat_env env);


/*@}*/ /* end of datatypes and special values group */


/**
 * \name Environment creation
 */
/*@{*/

/**
 * \brief Creates a new MathSAT configuration.
 * \return A new configuration.
 */
msat_config msat_create_config(void);

/**
 * \brief Creates a new MathSAT configuration with the default settings for
 * the given logic.
 *
 * \param logic An SMT-LIB logic name
 * \return A new configuration. In case of errors, a cfg s.t.
 *         MSAT_ERROR_CONFIG(cfg) is true is returned
 */
msat_config msat_create_default_config(const char *logic);

/**
 * \brief Creates a new MathSAT configuration by parsing the given data.
 *
 * The format for the configuration data is simply one "key = value" entry per
 * line. The data may include comments, prefixed by the # character (and
 * extending until the end of the line).
 *
 * \param data The configuration data to parse
 * \return A new configuration. In case of errors, a cfg s.t.
 *         MSAT_ERROR_CONFIG(cfg) is true is returned
 */
msat_config msat_parse_config(const char *data);

/**
 * \brief Creates a new MathSAT configuration by parsing the given file.
 *
 * See ::msat_parse_config for the format of the config file.
 *
 * \param f The configuration file to parse
 * \return A new configuration. In case of errors, a cfg s.t.
 *         MSAT_ERROR_CONFIG(cfg) is true is returned
 */
msat_config msat_parse_config_file(FILE *f);

/**
 * \brief Destroys a configuration.
 *
 * It is an error to destroy a configuration that is still being used by an
 * environment.
 * 
 * \param cfg The configuration to destroy.
 */ 
void msat_destroy_config(msat_config cfg);

/**
 * \brief Creates a new MathSAT environment from the given configuration.
 * \param cfg The configuration to use.
 * \return A new environment. Use ::MSAT_ERROR_ENV to check for errors
 */
msat_env msat_create_env(msat_config cfg);

/**
 * \brief Creates an environment that can share terms with its \a sibling
 * \param cfg The configuration to use.
 * \param sibling The environment with which to share terms.
 * \return A new environment. Use ::MSAT_ERROR_ENV to check for errors
 */
msat_env msat_create_shared_env(msat_config cfg, msat_env sibling);

/**
 * \brief Destroys an environment.
 * \param e The environment to destroy.
 */ 
void msat_destroy_env(msat_env e);

/**
 * \brief Performs garbage collection on the given environment
 *
 * This function will perform garbage collection on the given environment.
 * All the internal caches of the environment will be cleared (including those
 * in the active solvers and preprocessors). If the environment is not shared,
 * all the terms that are not either in \a tokeep or in the current asserted
 * formulas will be deleted.
 *
 * \param env The environment in which to operate.
 * \param tokeep List of terms to not delete.
 * \param num_tokeep Size of the \a tokeep array.
 * \return zero on success, nonzero on error.
 */
int msat_gc_env(msat_env env, msat_term *tokeep, size_t num_tokeep);

/**
 * \brief Sets an option in the given configuration.
 *
 * Notice that the best thing to do is set options right after having created
 * a configuration, before creating an environment with it. The library tries to
 * capture and report errors, but it does not always succeed.
 *
 * \param cfg The configuration in which to operate.
 * \param option The name of the option to set.
 * \param value The value for the option. For boolean options, use "true" or
 *        "false" (case matters). For flags, the value can be anything.
 * \return zero on success, nonzero on error.
 */
int msat_set_option(msat_config cfg, const char *option, const char *value);

/**
 * \brief Installs a custom termination test in the given environment
 *
 * The \a func function will be polled periodically by \a env,
 * terminating the current search as soon as \a func returns non-zero.
 *
 * \param env The environment in which to operate.
 * \param func The user-defined termination criterion. If it is NULL,
 *             no termination criterion will be used.
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted.
 * \return zero on success, nonzero on error
 */
int msat_set_termination_test(msat_env env, msat_termination_test func,
                              void *user_data);

/**
 * \brief returns the data type for Booleans in the given env.
 */
msat_type msat_get_bool_type(msat_env env);

/**
 * \brief returns the data type for rationals in the given env.
 */
msat_type msat_get_rational_type(msat_env env);

/**
 * \brief returns the data type for integers in the given env.
 */
msat_type msat_get_integer_type(msat_env env);

/**
 * \brief returns the data type for bit-vectors of the given width.
 */
msat_type msat_get_bv_type(msat_env env, size_t width);

/**
 * \brief returns the data type for arrays with indices of \a itp type and
 * elements of \a etp type.
 */
msat_type msat_get_array_type(msat_env env, msat_type itp, msat_type etp);

 /**
 * \brief returns the data type for floats with the given exponent and
 * significand/mantissa width.
 */
msat_type msat_get_fp_type(msat_env env, size_t exp_width, size_t mant_width);

/**
 * \brief returns the type for float rounding modes in the given env.
 */
msat_type msat_get_fp_roundingmode_type(msat_env env);

/**
 * \brief returns an atomic type with the given name in the given env.
 */
msat_type msat_get_simple_type(msat_env env, const char *name);

/**
 * \brief returns a function type in the given env.
 * \param env The environment in which to operate
 * \param param_types The types of the function arguments
 * \param num_params The arity of the function type
 * \param return_type The type of the return value
 * \return a function type
 */
msat_type msat_get_function_type(msat_env env, msat_type *param_types,
                                 size_t num_params, msat_type return_type);

/**
 * \brief checks whether the given type is bool.
 *
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \return 1 if the type is bool, 0 otherwise
 */
int msat_is_bool_type(msat_env env, msat_type tp);

/**
 * \brief checks whether the given type is rat.
 *
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \return 1 if the type is rat, 0 otherwise
 */
int msat_is_rational_type(msat_env env, msat_type tp);

/**
 * \brief checks whether the given type is int.
 *
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \return 1 if the type is int, 0 otherwise
 */
int msat_is_integer_type(msat_env env, msat_type tp);

/**
 * \brief checks whether the given type is a bit-vector.
 *
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \param out_width Pointer to a variable where to store the width of the
 *                  BV type in case of success (can be NULL)
 * \return 1 if the type is a bit-vector, 0 otherwise
 */
int msat_is_bv_type(msat_env env, msat_type tp, size_t *out_width);

/**
 * \brief checks whether the given type is an array.
 * 
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \param out_itp Pointer to a variable where to store the type of
 *                the array indices (can be NULL)
 * \param out_itp Pointer to a variable where to store the type of
 *                the array elements (can be NULL)
 * \return 1 if the type is an array, 0 otherwise
 */
int msat_is_array_type(msat_env env, msat_type tp,
                       msat_type *out_itp, msat_type *out_etp);

/**
 * \brief checks whether the given type is a float.
 *
 * \param env The environment in which to operate
 * \param tp The data type to check
 * \param out_exp_width Pointer to a variable where to store the width of the
 *                      exponent of the float in case of success (can be NULL)
 * \param out_mant_width Pointer to a variable where to store the width of the
 *                       significand/mantissa of the float in case of success
 *                       (can be NULL)
 * \return 1 if the type is a float, 0 otherwise
 */
int msat_is_fp_type(msat_env env, msat_type tp,
                    size_t *out_exp_width, size_t *out_mant_width);

/**
 * \brief checks whether the given type is a float rounding mode type.
 */
int msat_is_fp_roundingmode_type(msat_env env, msat_type tp);


/**
 * \brief checks whether two data types are the same
 * \return 1 if the types are the same, 0 otherwise
 */
int msat_type_equals(msat_type t1, msat_type t2);

/**
 * \brief Returns an internal string representation of a type
 *
 * The returned string can be useful for debugging purposes only, as
 * it is an internal representation of a type
 *
 * \param t A type.
 * \return a string reprsentation of \a t, or NULL in case of errors. The
 *         string must be dellocated by the caller with ::msat_free().
 */
char *msat_type_repr(msat_type t);


/**
 * \brief Declares a new uninterpreted function/constant
 *
 * \param e The environment of the declaration.
 * \param name A name for the function. It must be unique in the environment.
 * \param type The type of the function.
 * \return A constant declaration, or a val s.t. ::MSAT_ERROR_DECL(val) is true
 *         in case of errors.
 */
msat_decl msat_declare_function(msat_env e, const char *name, msat_type type);

/*@}*/

/**
 * \name Term creation
 */
/*@{*/

/**
 * \brief Returns a term representing logical truth.
 * \param e The environment of the definition
 * \return The term TRUE, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 * in case of errors.
 */
msat_term msat_make_true(msat_env e);

/**
 * \brief Returns a term representing logical falsity.
 * \param e The environment of the definition
 * \return The term FALSE, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_false(msat_env e);

/**
 * \brief Returns a term representing the equivalence of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument. Must have type ::MSAT_BOOL.
 * \param t2 The second argument. Must have type ::MSAT_BOOL.
 * \return The term t1 <-> t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_iff(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the logical OR of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument. Must have type ::MSAT_BOOL.
 * \param t2 The second argument. Must have type ::MSAT_BOOL.
 * \return The term t1 | t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_or(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the logical AND of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument. Must have type ::MSAT_BOOL.
 * \param t2 The second argument. Must have type ::MSAT_BOOL.
 * \return The term t1 & t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_and(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the logical negation of t1.
 * \param e The environment of the definition
 * \param t1 The argument to negate. Must have type ::MSAT_BOOL.
 * \return The term !t1, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_not(msat_env e, msat_term t1);

/**
 * \brief Returns a term representing the equivalence of t1 and t2.
 *
 * Note that this does not work If ::t1 and ::t2 have Boolean type (use
 * ::msat_make_iff() in that case).
 * 
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (t1 = t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_equal(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the equivalence of t1 and t2.
 *
 * This is a convenience function that calls either ::msat_make_equal() or
 * ::msat_make_iff(), according to the type of the arguments.
 * 
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (t1 = t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_eq(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns an atom representing (t1 <= t2).
 *
 * The arguments must have the same type. The exception is for integer
 * numbers, which can be casted to rational if necessary. 
 * 
 * \param e The environment of the definition
 * \param t1 The first argument. Must be of type rational or integer
 * \param t2 The second argument. Must be of type rational or integer
 * \return The term (t1 <= t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_leq(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns an expression representing (t1 + t2).
 *
 * The arguments must have the same type. The exception is for integer
 * numbers, which can be casted to rational if necessary. 
 * 
 * \param e The environment of the definition
 * \param t1 The first argument. Must be of type rational or integer
 * \param t2 The second argument. Must be of type rational or integer
 * \return The term (t1 + t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_plus(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns an expression representing (t1 * t2).
 *
 * The arguments must have the same type, with the usual exception for integer
 * numbers. 
 * 
 * \param e The environment of the definition
 * \param t1 The first argument. Must be of type rational or integer
 * \param t2 The second argument. Must be of type rational or integer
 * \return The term (t1 * t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_times(msat_env e, msat_term t1, msat_term t2);


/**
 * \brief Returns an expression representing (t1 / t2).
 *
 * The arguments must have the same type, with the usual exception for integer
 * numbers. 
 * 
 * \param e The environment of the definition
 * \param t1 The first argument. Must be of type rational or integer
 * \param t2 The second argument. Must be of type rational or integer
 * \return The term (t1 / t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_divide(msat_env e, msat_term t1, msat_term t2);


/**
 * \brief Returns an expression representing (t1 = t2 mod modulus).
 *
 * \param e The environment of the definition
 * \param modulus The value of the modulus. Must be > 0
 * \param t1 The first argument. 
 * \param t2 The second argument.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_int_modular_congruence(msat_env e, mpz_t modulus,
                                           msat_term t1, msat_term t2);

/**
 * \brief Returns an expression representing (floor t)
 * \param e The environment of the definition
 * \param t The argument. 
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_floor(msat_env e, msat_term t);

/**
 * \brief Returns the constant representing the pi number
 * \param e The environment of the definition
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_pi(msat_env e);

/**
 * \brief Returns an expression representing exp(t)
 * \param e The environment of the definition
 * \param t The argument.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_exp(msat_env e, msat_term t);

/**
 * \brief Returns an expression representing sin(t)
 * \param e The environment of the definition
 * \param t The argument.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_sin(msat_env e, msat_term t);

/**
 * \brief Returns an expression representing the natural log of t
 * \param e The environment of the definition
 * \param t The argument.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_log(msat_env e, msat_term t);

/**
 * \brief Returns an expression representing tb to the power of te
 * \param e The environment of the definition
 * \param tb The base of the power
 * \param te The exponent of the power
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_pow(msat_env e, msat_term tb, msat_term te);

/**
 * \brief Returns an expression representing arcsin(t)
 * \param e The environment of the definition
 * \param t The argument
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_asin(msat_env e, msat_term t);

/**
 * \brief Returns an expression representing an integer or rational number.
 *
 * \param e The environment of the definition
 * \param num_rep A string representation for the number
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_number(msat_env e, const char *num_rep);

/**
 * \brief Returns an expression representing an integer or rational number.
 *
 * \param e The environment of the definition
 * \param value The value for the number
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_int_number(msat_env e, int value);

/**
 * \brief Returns an expression representing an integer or rational number.
 *
 * \param e The environment of the definition
 * \param value The value for the number
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_mpq_number(msat_env e, mpq_t value);

/**
 * \brief Returns an expression representing a term if-then-else construct.
 *
 * The two arguments ::tt and ::te must have compatible types.
 *
 * \param e The environment of the definition
 * \param c The condition of the test. Must be of type ::MSAT_BOOL
 * \param tt The "then" branch
 * \param te The "else" branch
 * 
 * \return The term representing the if-then-else, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_term_ite(msat_env e, msat_term c,
                             msat_term tt, msat_term te);

/**
 * \brief Creates a constant from a declaration.
 * \param e The environment of the definition
 * \param var The declaration of the constant. Must come from the same
 *            environment
 * \return The term representing the constant, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_make_constant(msat_env e, msat_decl var);

/**
 * \brief Creates an uninterpreted function application.
 *
 * The number and type of the arguments must match those of the declaration.
 * 
 * \param e The environment of the definition
 * \param func The declaration of the function
 * \param args The actual parameters
 * \return The term representing the function/predicate call, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors. */
msat_term msat_make_uf(msat_env e, msat_decl func, msat_term args[]);

/**
 * \brief Creates an array read operation.
 *
 * \param e The environment of the definition
 * \param arr The array term
 * \param idx The index term
 * \return The term representing the array read, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors. */
msat_term msat_make_array_read(msat_env e, msat_term arr, msat_term idx);

/**
 * \brief Creates an array write operation.
 *
 * \param e The environment of the definition
 * \param arr The array term
 * \param idx The index term
 * \param elem The element term
 * \return The term representing the array write, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors. */
msat_term msat_make_array_write(msat_env e, msat_term arr, msat_term idx,
                                msat_term elem);

/**
 * \brief Creates a constant array.
 *
 * \param e The environment of the definition
 * \param arrtp The type of the return array
 * \param elem The element term
 * \return The term representing the constant array filled with "elem",
 *         or a t s.t. ::MSAT_ERROR_TERM(t) is true in case of errors. */
msat_term msat_make_array_const(msat_env e, msat_type arrtp, msat_term elem);

/**
 * \brief Returns an expression representing a bit-vector number.
 *
 * \param e The environment of the definition
 * \param num_rep A string representation for the number.
 *                The number must be non-negative.
 * \param width The width in bits of the number
 * \param base The base of the representation. Can be 2, 10 or 16.
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_number(msat_env e, const char *num_rep, size_t width,
                              size_t base);

/**
 * \brief Returns an expression representing a bit-vector number.
 *
 * \param e The environment of the definition
 * \param value The value for the number. It must be non-negative.
 * \param width The width in bits of the number
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_int_number(msat_env e, int value, size_t width);

/**
 * \brief Returns an expression representing a bit-vector number.
 *
 * \param e The environment of the definition
 * \param value The value for the number. It must be non-negative.
 * \param width The width in bits of the number
 * 
 * \return The numeric term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_mpz_number(msat_env e, mpz_t value, size_t width);

/**
 * \brief Returns a term representing the concatenation of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument. 
 * \param t2 The second argument.
 * \return The term t1 :: t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_concat(msat_env e, msat_term t1, msat_term t2);


/**
 * \brief Returns a term representing the selection of t[msb:lsb].
 * \param e The environment of the definition
 * \param msb The most significant bit of the selection.
 * \param lsb The least significant bit of the selection.
 * \param t The argument.
 * \return The term t[msb:lsb], or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_extract(msat_env e, size_t msb, size_t lsb, msat_term t);

/**
 * \brief Returns a term representing the bit-wise OR of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument. 
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 | t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_or(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the bit-wise XOR of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 xor t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_xor(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the bit-wise AND of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 \& t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_and(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the bit-wise negation of t.
 * \param e The environment of the definition
 * \param t The argument to negate.
 * \return The term !t, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_not(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the logical left shift of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument. 
 * \param t2 The second argument.
 * \pre \a t1 and \a t2 must have the same width.
 * \return The term t1 << t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_lshl(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the logical right shift of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 >> t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_lshr(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the arithmetic right shift of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 >> t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_ashr(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the zero extension of t.
 * \param e The environment of the definition
 * \param amount The amount of the extension
 * \param t The first argument. 
 * \return The term zext(amount, t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_zext(msat_env e, size_t amount, msat_term t);

/**
 * \brief Returns a term representing the sign extension of t1 by amount.
 * \param e The environment of the definition
 * \param amount The amount of the extension
 * \param t The first argument.
 * \return The term sext(amount, t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_sext(msat_env e, size_t amount, msat_term t);

/**
 * \brief Returns a term representing the addition of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 + t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_plus(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the subtraction of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 - t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_minus(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the negation of t, te two's-complement.
 * \param e The environment of the definition
 * \param t The argument.
 * \return The term -t, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_neg(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the multiplication of t1 and t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 * t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_times(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the unsigned division of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument. 
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 / t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_udiv(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the unsigned remainder of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 % t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_urem(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the signed division of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 / t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_sdiv(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the signed remainder of t1 by t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 % t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_srem(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the unsigned t1 < t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 < t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_ult(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the unsigned t1 <= t2.
 * \param e The environment of the definition
 * \param t1 The first argument. 
 * \param t2 The second argument. 
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 <= t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_uleq(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the signed t1 < t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 < t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_slt(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the signed t1 <= t2.
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term t1 <= t2, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_sleq(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the left rotation of \a 1 by
 *        \a amount bits.
 * \param e The environment of the definition
 * \param amount The amount of the rotation
 * \param t The argument of the rotation.
 * \return The term rol(amount, t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_rol(msat_env e, size_t amount, msat_term t);

/**
 * \brief Returns a term representing the right rotation of \a 1 by
 *        \a amount bits.
 * \param e The environment of the definition
 * \param amount The amount of the rotation
 * \param t The argument of the rotation.
 * \return The term ror(amount, t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_ror(msat_env e, size_t amount, msat_term t);

/**
 * \brief Returns a term representing the comparison of \a t1 and \a t2,
 *        resulting in a bit-vector of size 1
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \pre \p t1 and \p t2 must have the same width.
 * \return The term bvcomp(t1, t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_bv_comp(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP rounding mode ROUND_TO_NEAREST_EVEN
 * \param e The environment of the definition
 * \return The term ROUND_TO_NEAREST_EVEN, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_make_fp_roundingmode_nearest_even(msat_env e);

/**
 * \brief Returns a term representing the FP rounding mode ROUND_TO_ZERO
 * \param e The environment of the definition
 * \return The term ROUND_TO_ZERO, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_make_fp_roundingmode_zero(msat_env e);

/**
 * \brief Returns a term representing the FP rounding mode ROUND_TO_PLUS_INF
 * \param e The environment of the definition
 * \return The term ROUND_TO_PLUS_INF, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_make_fp_roundingmode_plus_inf(msat_env e);

/**
 * \brief Returns a term representing the FP rounding mode ROUND_TO_MINUS_INF
 * \param e The environment of the definition
 * \return The term ROUND_TO_MINUS_INF, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_make_fp_roundingmode_minus_inf(msat_env e);

/**
 * \brief Returns a term representing the FP equality predicate between
 *        \a t1 and \a t2.
 *
 * FP equality is different from the "regular" equality predicate in the
 * handling of NaN values: (fpeq NaN NaN) is always false, whereas (= NaN NaN)
 * is always true
 *        
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (fpeq t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_equal(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP < predicate between
 *        \a t1 and \a t2.
 *        
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (fplt t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_lt(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP <= predicate between
 *        \a t1 and \a t2.
 *        
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (fpleq t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_leq(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP negation of \a t.
 *        
 * \param e The environment of the definition
 * \param t The argument to negate.
 * \return The term (fpneg t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_neg(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the FP addition of \a t1 and \a t2,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (+ rounding t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_plus(msat_env e, msat_term rounding,
                            msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP subtraction of \a t1 and \a t2,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (- rounding t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_minus(msat_env e, msat_term rounding,
                             msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP multiplication of \a t1 and \a t2,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (* rounding t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_times(msat_env e, msat_term rounding,
                             msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP division of \a t1 and \a t2,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (/ rounding t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_div(msat_env e, msat_term rounding,
                           msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP square root of \a t,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t The sqrt argument.
 * \return The term (sqrt rounding t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_sqrt(msat_env e, msat_term rounding, msat_term t);

/**
 * \brief Returns a term representing the FP absolute value of \a t.
 *        
 * \param e The environment of the definition
 * \param t The abs argument.
 * \return The term (abs t), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_abs(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the FP min between \a t1 and \a t2.
 *        
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (min t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_min(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP max between \a t1 and \a t2.
 *        
 * \param e The environment of the definition
 * \param t1 The first argument.
 * \param t2 The second argument.
 * \return The term (max t1 t2), or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_fp_max(msat_env e, msat_term t1, msat_term t2);

/**
 * \brief Returns a term representing the FP round to integral of \a t,
 *        according to the given \a rounding mode.
 *        
 * \param e The environment of the definition
 * \param rounding The desired rounding mode.
 * \param t The argument.
 * \return The term (fp.roundToIntegral rounding t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_round_to_int(msat_env e, msat_term rounding,
                                    msat_term t);

/**
 * \brief Returns a term representing the FP format conversion of the given
 *        input term.
 *        
 * \param e The environment of the definition
 * \param exp_w The target exponent width.
 * \param mant_w The target mantissa width.
 * \param rounding The desired rounding mode.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_cast(msat_env e, size_t exp_w, size_t mant_w,
                            msat_term rounding, msat_term t);

/**
 * \brief Returns a term representing the conversion of a FP term to a signed
 *        bit-vector.
 *        
 * \param e The environment of the definition
 * \param width The target bit-vector width.
 * \param rounding The desired rounding mode.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_to_sbv(msat_env e, size_t width,
                              msat_term rounding, msat_term t);
msat_term msat_make_fp_to_bv(msat_env e, size_t width,
                             msat_term rounding, msat_term t);


/**
 * \brief Returns a term representing the conversion of a FP term to
 *        an unsigned bit-vector.
 *        
 * \param e The environment of the definition
 * \param width The target bit-vector width.
 * \param rounding The desired rounding mode.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_to_ubv(msat_env e, size_t width,
                              msat_term rounding, msat_term t);

/**
 * \brief Returns a term representing the conversion of a signed bit-vector
 *        term to FP.
 *        
 * \param e The environment of the definition
 * \param exp_w The target exponent width.
 * \param mant_w The target mantissa width.
 * \param rounding The desired rounding mode.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_from_sbv(msat_env e, size_t exp_w, size_t mant_w,
                                msat_term rounding, msat_term t);

/**
 * \brief Returns a term representing the conversion of an unsigned bit-vector
 *        term to FP.
 *        
 * \param e The environment of the definition
 * \param exp_w The target exponent width.
 * \param mant_w The target mantissa width.
 * \param rounding The desired rounding mode.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_from_ubv(msat_env e, size_t exp_w, size_t mant_w,
                                msat_term rounding, msat_term t);

/**
 * \brief Returns a term for interpreting a FP term as a bit-vector.
 *
 * This is different from ::make_fp_to_sbv in that the latter takes the integer
 * part of the FP number and stores it in a bit-vector, while this function
 * simply takes the bits of the representation of the input and interprets
 * them as a bit-vector (of size 1+ width of exponent + width of mantissa).
 *        
 * \param e The environment of the definition
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_as_ieeebv(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the FP number whose IEEE 754 encoding is
 * the given bit-vector.
 *        
 * \param e The environment of the definition
 * \param exp_w The target exponent width.
 * \param mant_w The target mantissa width.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_from_ieeebv(msat_env e, size_t exp_w, size_t mant_w,
                                   msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is NaN.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (isnan t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_isnan(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is infinity.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (isinf t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_isinf(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is zero.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (iszero t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_iszero(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is a subnormal.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (issubnormal t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_issubnormal(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is a normal.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (isnormal t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_isnormal(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is negative.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (isneg t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_isneg(msat_env e, msat_term t);

/**
 * \brief Returns the predicate for testing whether a FP term is positive.
 *        
 * \param e The environment of the definition
 * \param t The argument to test.
 * \return The term representing (ispos t), or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_ispos(msat_env e, msat_term t);

/**
 * \brief Returns the FP term representing +Inf of the given format.
 *        
 * \param e The environment of the definition
 * \param exp_w The desired exponent width
 * \param mant_w The desired mantissa width
 * \return A term representing +Inf, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_plus_inf(msat_env e, size_t exp_w, size_t mant_w);

/**
 * \brief Returns the FP term representing -Inf of the given format.
 *        
 * \param e The environment of the definition
 * \param exp_w The desired exponent width
 * \param mant_w The desired mantissa width
 * \return A term representing -Inf, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_minus_inf(msat_env e, size_t exp_w, size_t mant_w);

/**
 * \brief Returns the FP term representing NaN of the given format.
 *        
 * \param e The environment of the definition
 * \param exp_w The desired exponent width
 * \param mant_w The desired mantissa width
 * \return A term representing NaN, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_nan(msat_env e, size_t exp_w, size_t mant_w);

/**
 * \brief Creates an FP number from a rational number.
 *        
 * \param e The environment of the definition
 * \param num_rep A string representation for the rational number
 * \param exp_w The desired exponent width
 * \param mant_w The desired mantissa width
 * \param rounding The desired rounding mode.
 * \return The numeric term, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_rat_number(msat_env e, const char *num_rep,
                                  size_t exp_w, size_t mant_w,
                                  msat_term rounding);

/**
 * \brief Creates an FP number from a string of bits.
 *        
 * \param e The environment of the definition
 * \param num_rep A string representation of a base-10 integer number
 * \param exp_w The desired exponent width
 * \param mant_w The desired mantissa width
 * \return The numeric term, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_fp_bits_number(msat_env e, const char *bits,
                                   size_t exp_w, size_t mant_w);

/**
 * \brief Returns a term representing the conversion of an int to a bit-vector.
 *        
 * \param e The environment of the definition
 * \param width The target bit-vector width.
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_int_to_bv(msat_env e, size_t width, msat_term t);

/**
 * \brief Returns a term representing the conversion of an unsigned bit-vector
 *        to an int.
 *        
 * \param e The environment of the definition
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_int_from_ubv(msat_env e, msat_term t);

/**
 * \brief Returns a term representing the conversion of a signed bit-vector
 *        to an int.
 *        
 * \param e The environment of the definition
 * \param t The argument to convert.
 * \return The term representing the conversion, or a t s.t.
 *         ::MSAT_ERROR_TERM(t) is true in case of errors.
 */
msat_term msat_make_int_from_sbv(msat_env e, msat_term t);

/**
 * \brief Returns a term resulting from universally quantifying
 *        the variable var in the term body.
 * \param e The environment of the definition
 * \param var The term representing the quantified variable.
 * \param body The body of the quantifier. Must have type ::MSAT_BOOL.
 * \return The term forall var body, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_forall(msat_env e, msat_term var, msat_term body);

/**
 * \brief Returns a term resulting from existentially quantifying
 *        the variable var in the term body.
 * \param e The environment of the definition
 * \param var The term representing the quantified variable.
 * \param body The body of the quantifier. Must have type ::MSAT_BOOL.
 * \return The term exists var body, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_exists(msat_env e, msat_term var, msat_term body);

/**
 * \brief Returns a term representing a variable, which can be used
 *        for existential or universal quantification.
 * \param e The environment of the definition
 * \param name The name of the variable.
 * \param type The type of the variable.
 * \return The term for the variable, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_variable(msat_env e, const char *name, msat_type type);

/**
 * \brief Returns a term resulting from existentially quantifying
 *        the given constants in the given term.
 * \param e The environment of the definition
 * \param t The term whose constants should be existentially quantified.
 * \param args The list of constants to quantify.
 * \param n The size of the list of constants.
 * \return The term exists constants body, or a t s.t. ::MSAT_ERROR_TERM(t) is
 *         true in case of errors.
 */
msat_term msat_existentially_quantify(msat_env e, msat_term t, msat_term args[],
                                      size_t n);

/**
 * \brief Creates a term from a declaration and a list of arguments
 *
 * \param e The environment in which to create the term
 * \param d The declaration
 * \param args The arguments
 * \pre The length of \a args should be equal to the arity of \a d
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_term(msat_env e, msat_decl d, msat_term args[]);

/**
 * \brief Creates a term in \a e from an equivalent term \a t that was created
 *        in \a src.
 *
 * \param e The environment in which to create the term
 * \param t The term to copy
 * \param src The environment in which \a t was created
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_make_copy_from(msat_env e, msat_term t, msat_env src);

/*@}*/ /* end of term creation group */

/**
 * \name Term access and navigation
 */
/*@{*/

/**
 * \brief Returns a numeric identifier for \a t
 *
 * The returned value is guaranteed to be unique within the environment in
 * which \a t was defined. Therefore, it can be used to test two terms for
 * equality, as well as a hash value.
 *
 * \param t A term. 
 * \return a unique (within the defining env) numeric identifier
 */
size_t msat_term_id(msat_term t);

/**
 * \brief Returns the arity of \a t
 * \param t A term. 
 * \return The number of arguments of \a t
 */
size_t msat_term_arity(msat_term t);

/**
 * \brief Returns the nth argument of \a t
 * \param t A term. 
 * \param n The index of the argument. Must be lower than the arity of \a t
 * \return The nth argument of arguments of \a t
 */
msat_term msat_term_get_arg(msat_term t, size_t n);

/**
 * \brief Returns the type of \a t
 * \param t A term. 
 * \return The type of \a t
 */
msat_type msat_term_get_type(msat_term t);

/**
 * \brief Checks whether \a t is the TRUE term
 * \param t A term. 
 * \return nonzero if \a t is TRUE
 */
int msat_term_is_true(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is the FALSE term
 * \param t A term. 
 * \return nonzero if \a t is FALSE
 */
int msat_term_is_false(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a boolean constant
 * \param t A term. 
 * \return nonzero if \a t is a constant of type ::MSAT_BOOL
 */
int msat_term_is_boolean_constant(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an atom
 * \param t A term. 
 * \return nonzero if \a t is an atom, i.e. either a boolean constant or
 *         a relation between terms
 */
int msat_term_is_atom(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a number
 * \param t A term. 
 * \return nonzero if \a t is a number
 */
int msat_term_is_number(msat_env e, msat_term t);

/**
 * \brief converts the given term to an mpq_t rational number
 *
 * The term must be a number, otherwise an error is reported.
 *
 * \param e the environment in which to operate 
 * \param t the number to convert
 * \param out the result of the conversion. Before calling this function,
 *            \a out should be initialized with a call to mpq_init()
 * \return zero on success, nonzero on error
 */
int msat_term_to_number(msat_env e, msat_term t, mpq_t out);

/**
 * \brief Checks whether \a t is an AND
 * \param t A term. 
 * \return nonzero if \a t is an AND
 */
int msat_term_is_and(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an OR
 * \param t A term. 
 * \return nonzero if \a t is an OR
 */
int msat_term_is_or(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a NOT
 * \param t A term. 
 * \return nonzero if \a t is a NOT
 */
int msat_term_is_not(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an equivalence between boolean terms
 * \param t A term. 
 * \return nonzero if \a t is an IFF
 */
int msat_term_is_iff(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a term if-then-else
 * \param t A term. 
 * \return nonzero if \a t is a term if-then-else
 */
int msat_term_is_term_ite(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a constant
 * \param t A term. 
 * \return nonzero if \a t is a constant
 */
int msat_term_is_constant(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an uninterpreted function application
 * \param t A term. 
 * \return nonzero if \a t is a uf application
 */
int msat_term_is_uf(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an equality
 * \param t A term. 
 * \return nonzero if \a t is an equality atom
 */
int msat_term_is_equal(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (t1 <= t2) atom
 * \param t A term. 
 * \return nonzero if \a t is a (t1 <= t2) atom
 */
int msat_term_is_leq(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (t1 + t2) expression
 * \param t A term. 
 * \return nonzero if \a t is a (t1 + t2) expression
 */
int msat_term_is_plus(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (t1 * t2) expression
 * \param t A term. 
 * \return nonzero if \a t is a (t1 * t2) expression
 */
int msat_term_is_times(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (t1 / t2) expression
 * \param t A term. 
 * \return nonzero if \a t is a (t1 / t2) expression
 */
int msat_term_is_divide(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an integer modular congruence expression.
 *        If so, stores in \a out_mod the value of the modulus as a GMP bigint
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is an integer modular congruence
 */
int msat_term_is_int_modular_congruence(msat_env e, msat_term t, mpz_t out_mod);

/**
 * \brief Checks whether \a t is a (floor t1) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a floor expression
 */
int msat_term_is_floor(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a the pi constant
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is the pi constant
 */
int msat_term_is_pi(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (exp t1) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a exp expression
 */
int msat_term_is_exp(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (sin t1) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a sin expression
 */
int msat_term_is_sin(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (log t1) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a log expression
 */
int msat_term_is_log(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (pow t1 t2) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a pow expression
 */
int msat_term_is_pow(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (asin t1) expression
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a asin expression
 */
int msat_term_is_asin(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an array read
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is an array read
 */
int msat_term_is_array_read(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an array write
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is an array write
 */
int msat_term_is_array_write(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a constant array
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a constant array
 */
int msat_term_is_array_const(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a BV concatenation
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a concatenation 
 */
int msat_term_is_bv_concat(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a BV extraction
 * \param e The environment in which to operate
 * \param t A term.
 * \param out_msb If not NULL, the msb of the selection will be stored here
 * \param out_lsb If not NULL, the lsb of the selection will be stored here
 * \return nonzero if \a t is an extraction
 */
int msat_term_is_bv_extract(msat_env e, msat_term t,
                            size_t *out_msb, size_t *out_lsb);

/**
 * \brief Checks whether \a t is a bit-wise or
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-wise or
 */
int msat_term_is_bv_or(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-wise xor
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-wise xor
 */
int msat_term_is_bv_xor(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-wise and
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-wise and
 */
int msat_term_is_bv_and(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-wise not
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-wise not
 */
int msat_term_is_bv_not(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector addition
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector addition
 */
int msat_term_is_bv_plus(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector subtraction
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector subtraction
 */
int msat_term_is_bv_minus(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector multiplication
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector multiplication
 */
int msat_term_is_bv_times(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector unary negation
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector unary negation
 */
int msat_term_is_bv_neg(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector unsigned division
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector unsigned division
 */
int msat_term_is_bv_udiv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector unsigned remainder
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector unsigned remainder
 */
int msat_term_is_bv_urem(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector signed division
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector signed division
 */
int msat_term_is_bv_sdiv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector signed remainder
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector signed remainder
 */
int msat_term_is_bv_srem(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector unsigned lt
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector unsigned lt
 */
int msat_term_is_bv_ult(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector unsigned leq
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector unsigned leq
 */
int msat_term_is_bv_uleq(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector signed lt
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector signed lt
 */
int msat_term_is_bv_slt(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a bit-vector signed leq
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a bit-vector signed leq
 */
int msat_term_is_bv_sleq(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a logical shift left
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a logical shift left
 */
int msat_term_is_bv_lshl(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a logical shift right
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is a logical shift right
 */
int msat_term_is_bv_lshr(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an arithmetic shift right
 * \param e The environment in which to operate
 * \param t A term. 
 * \return nonzero if \a t is an arithmetic shift right
 */
int msat_term_is_bv_ashr(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a zero extension
 * \param e The environment in which to operate
 * \param t A term.
 * \param out_amount If not NULL, the amount of the zero extension
 *                   will be stored here
 * \return nonzero if \a t is a zero extension
 */
int msat_term_is_bv_zext(msat_env e, msat_term t, size_t *out_amount);

/**
 * \brief Checks whether \a t is a sign extension
 * \param e The environment in which to operate
 * \param t A term.
 * \param out_amount If not NULL, the amount of the sign extension
 *                   will be stored here
 * \return nonzero if \a t is a sign extension
 */
int msat_term_is_bv_sext(msat_env e, msat_term t, size_t *out_amount);

/**
 * \brief Checks whether \a t is a rotate left
 * \param e The environment in which to operate
 * \param t A term.
 * \param out_amount If not NULL, the amount of the left rotation
 *                   will be stored here
 * \return nonzero if \a t is a rotate left
 */
int msat_term_is_bv_rol(msat_env e, msat_term t, size_t *out_amount);

/**
 * \brief Checks whether \a t is a rotate right
 * \param e The environment in which to operate
 * \param t A term.
 * \param out_amount If not NULL, the amount of the right rotation
 *                   will be stored here
 * \return nonzero if \a t is a rotate right
 */
int msat_term_is_bv_ror(msat_env e, msat_term t, size_t *out_amount);

/**
 * \brief Checks whether \a t is a BV comparison
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a BV comparison
 */
int msat_term_is_bv_comp(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is the ROUND_TO_NEAREST_EVEN FP
 *        rounding mode constant
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is ROUND_TO_NEAREST_EVEN
 */
int msat_term_is_fp_roundingmode_nearest_even(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is the ROUND_TO_ZERO FP
 *        rounding mode constant
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is ROUND_TO_ZERO
 */
int msat_term_is_fp_roundingmode_zero(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is the ROUND_TO_PLUS_INF FP
 *        rounding mode constant
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is ROUND_TO_PLUS_INF
 */
int msat_term_is_fp_roundingmode_plus_inf(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is the ROUND_TO_MINUS_INF FP
 *        rounding mode constant
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is ROUND_TO_MINUS_INF
 */
int msat_term_is_fp_roundingmode_minus_inf(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP equality
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP equality
 */
int msat_term_is_fp_equal(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP less than
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP less than
 */
int msat_term_is_fp_lt(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP <=
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP <=
 */
int msat_term_is_fp_leq(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP negation
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP negation
 */
int msat_term_is_fp_neg(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP plus
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP plus
 */
int msat_term_is_fp_plus(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP minus
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP minus
 */
int msat_term_is_fp_minus(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP times
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP times
 */
int msat_term_is_fp_times(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP div
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP div
 */
int msat_term_is_fp_div(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP sqrt
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP sqrt
 */
int msat_term_is_fp_sqrt(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP abs
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP abs
 */
int msat_term_is_fp_abs(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP min
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP min
 */
int msat_term_is_fp_min(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP max
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP max
 */
int msat_term_is_fp_max(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP round to integer
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP round to integer
 */
int msat_term_is_fp_round_to_int(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP cast
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP cast
 */
int msat_term_is_fp_cast(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP to signed BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP to BV conversion
 */
int msat_term_is_fp_to_sbv(msat_env e, msat_term t);
int msat_term_is_fp_to_bv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP to unsigned BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP to BV conversion
 */
int msat_term_is_fp_to_ubv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP from signed BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP from signed BV conversion
 */
int msat_term_is_fp_from_sbv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP from unsigned BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP from unsigned BV conversion
 */
int msat_term_is_fp_from_ubv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP as BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP as BV conversion
 */
int msat_term_is_fp_as_ieeebv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP from IEEE BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP from unsigned BV conversion
 */
int msat_term_is_fp_from_ieeebv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP isnan predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP isnan predicate
 */
int msat_term_is_fp_isnan(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP isinf predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP isinf predicate
 */
int msat_term_is_fp_isinf(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP iszero predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP iszero predicate
 */
int msat_term_is_fp_iszero(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP issubnormal predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP iszero predicate
 */
int msat_term_is_fp_issubnormal(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP isnormal predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP isnormal predicate
 */
int msat_term_is_fp_isnormal(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP isneg predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP isneg predicate
 */
int msat_term_is_fp_isneg(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a FP ispos predicate
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a FP ispos predicate
 */
int msat_term_is_fp_ispos(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a int to BV conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a int to BV conversion
 */
int msat_term_is_int_to_bv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an unsigned BV to int conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is an unsigned BV to int conversion
 */
int msat_term_is_int_from_ubv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a signed BV to int conversion
 * \param e The environment in which to operate
 * \param t A term.
 * \return nonzero if \a t is a signed BV to int conversion
 */
int msat_term_is_int_from_sbv(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a quantifier
 * \param t A term.
 * \return nonzero if \a t is a quantifier
 */
int msat_term_is_quantifier(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a universal quantifier
 * \param t A term.
 * \return nonzero if \a t is a universal quantifier
 */
int msat_term_is_forall(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is an existential quantifier
 * \param t A term.
 * \return nonzero if \a t is an existential quantifier
 */
int msat_term_is_exists(msat_env e, msat_term t);

/**
 * \brief Checks whether \a t is a (free or bound) variable
 * \param t A term.
 * \return nonzero if \a t is a variable
 */
int msat_term_is_variable(msat_env e, msat_term t);

/**
 * \brief visits the DAG of the given term \a t, calling the callback \a func
 * for every suberm
 *
 * \param e The environment in which to operate
 * \param t The term to visit
 * \param func The callback function
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted
 * \return zero on success, nonzero on error
 */ 
int msat_visit_term(msat_env e, msat_term t, msat_visit_term_callback func,
                    void *user_data);

/**
 * \brief substitutes the terms in \a to_subst with \a values in \a t
 *
 * \param e The environment in which to operate
 * \param t The term to apply the substitution to
 * \param n The number of terms to substitute
 * \param to_subst The terms to substitute
 * \param values The values to substitute
 *
 * \return The result of the substitution, or a t s.t. ::MSAT_ERROR_TERM(t)
 *         is true in case of errors.
 */
msat_term msat_apply_substitution(msat_env e, msat_term t, size_t n,
                                  msat_term *to_subst, msat_term *values);

/**
 * \brief Returns the declaration of the given \a symbol in the given
 *        environment (if any)
 *
 * If \a symbol is not declared in \a e, the returned value \a ret will be s.t.
 * MSAT_ERROR_DECL(ret) is true
 *
 * \param e The environment in which to operate
 *
 * \return The declaration of \a symbol in \a e, or a \a ret
 *         s.t. MSAT_ERROR_DECL(ret) is true
 */
msat_decl msat_find_decl(msat_env e, const char *symbol);

/**
 * \brief Returns the declaration associated to \a t (if any)
 *
 * If \a t is not a constant or a function application, the returned value \a
 * ret will be s.t. MSAT_ERROR_DECL(ret) is true
 *
 * \param t The term for which to retrieve the declaration
 * 
 * \return If \a t is a constant, its declaration is returned; if it
 *         is an uif, the declaration of the function is returned; otherwise,
 *         a \a ret s.t. MSAT_ERROR_DECL(ret) is true is returned
 */
msat_decl msat_term_get_decl(msat_term t);

/**
 * \brief Returns a numeric identifier for the input declaration
 *
 * The returned value is guaranteed to be unique within the environment in
 * which \a d was defined. Therefore, it can be used to test
 * two declarations for equality, as well as a hash value.
 *
 * \param d A declaration. 
 * \return a unique (within the defining env) numeric identifier
 */
size_t msat_decl_id(msat_decl d);

/**
 * \brief Returns the symbol tag associated to the given declaration
 *
 * \param e The environment in which to operate
 * \param d A declaration
 * \return the tag of the declaration
 */
msat_symbol_tag msat_decl_get_tag(msat_env e, msat_decl d);

/**
 * \brief Returns the return type of the given declaration
 *
 * The return type for a constant is simply the constant's type.
 *
 * \param d A declaration
 *
 * \return The return type. In case of error, MSAT_U is returned.
 */
msat_type msat_decl_get_return_type(msat_decl d);

/**
 * \brief Returns the arity (number of arguments) of the given
 * declaration.
 *
 * \param d A declaration
 *
 * \return The arity of the declaration.
 */
size_t msat_decl_get_arity(msat_decl d);

/**
 * \brief Returns the type of the given argument for the input declaration.
 *
 * \param d A declaration
 * \param n The index of the argument for which the type is needed
 *
 * \return The type of the given argument, or MSAT_U on error.
 */
msat_type msat_decl_get_arg_type(msat_decl d, size_t n);

/**
 * \brief Returns the name corresponding to the given declaration.
 *
 * \param d A declaration
 *
 * \return The name of the given declaration. The returned string must be
 *         deallocated by the user with ::msat_free(). NULL is returned in
 *         case of error.
 */
char *msat_decl_get_name(msat_decl d);


/**
 * \brief Returns an internal string representation of a declaration.
 *
 * The returned string can be useful for debugging purposes only, as
 * it is an internal representation of a declaration
 *
 * \param d A declaration.
 * \return a string reprsentation of \a d, or NULL in case of errors. The
 *         string must be dellocated by the caller with ::msat_free().
 */
char *msat_decl_repr(msat_decl d);


/**
 * \brief Returns an internal string representation of a term
 *
 * The returned string can be useful for debugging purposes only, as
 * it is an internal representation of a term
 *
 * \param t A term.
 * \return a string reprsentation of \a t, or NULL in case of errors. The
 *         string must be dellocated by the caller with ::msat_free().
 */
char *msat_term_repr(msat_term t);


/*@}*/ /* end of Term access and navigation group */

/**
 * \name Term parsing/printing
 */

/**
 * \brief Creates a term from its string representation
 *
 * The syntax of \a repr is that of the SMT-LIB v2. All
 * the variables and functions must have been previously declared in \a e.
 *
 * \param e The environment of the definition
 * \param repr The string to parse, in SMT-LIB v2 syntax
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_from_string(msat_env e, const char *data);


/**
 * \brief Creates a term from a string in SMT-LIB v1 format.
 *
 * \param e The environment in which to create the term.
 * \param data The string representation in SMT-LIB v1 format.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_from_smtlib1(msat_env e, const char *data);

/**
 * \brief Creates a term from a file in SMT-LIB v1 format.
 *
 * \param e The environment in which to create the term.
 * \param f The file in SMT-LIB v1 format.
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_from_smtlib1_file(msat_env e, FILE *f);

/**
 * \brief Creates a term from a string in SMT-LIB v2 format.
 *
 * \param e The environment in which to create the term.
 * \param data The string representation in SMT-LIB v2 format.
 *             It can't contain commands other than functions and type
 *             declarations, definitions, and assertions
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_from_smtlib2(msat_env e, const char *data);

/**
 * \brief Creates a term from a file in SMT-LIB v2 format.
 *
 * \param e The environment in which to create the term.
 * \param f The file in SMT-LIB v2 format.
 *          It can't contain commands other than functions and type
 *          declarations, definitions, and assertions
 * \return The created term, or a t s.t. ::MSAT_ERROR_TERM(t) is true
 *         in case of errors.
 */
msat_term msat_from_smtlib2_file(msat_env e, FILE *f);


/**
 * \brief Converts the given \a term to SMT-LIB v1 format
 *
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * 
 * \return a string in SMT-LIB v1 format for the formula represented by \a
 *         term, or NULL in case of errors. If not NULL, the returned string
 *         must be deallocated by the user with ::msat_free().
 */ 
char *msat_to_smtlib1(msat_env e, msat_term term);


/**
 * \brief Dumps the given \a term in SMT-LIB v1 format to the given output file
 *
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * \param out The output file
 * \return zero on success, nonzero on error.
 */ 
int msat_to_smtlib1_file(msat_env e, msat_term term, FILE *out);


/**
 * \brief Converts the given \a term to SMT-LIB v2 format
 *
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * 
 * \return a string in SMT-LIB v2 format for the formula represented by \a
 *         term, or NULL in case of errors. If not NULL, the returned string
 *         must be deallocated by the user with ::msat_free().
 */ 
char *msat_to_smtlib2(msat_env e, msat_term term);


/**
 * \brief Dumps the given \a term in SMT-LIB v2 format to the given output file
 *
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * \param out The output file
 * \return zero on success, nonzero on error.
 */ 
int msat_to_smtlib2_file(msat_env e, msat_term term, FILE *out);


/**
 * \brief Converts the given \a term to SMT-LIB v2 format
 * 
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * \param logic_name Name of the SMT-LIBv2 logic for the output. Can be NULL
 * \param use_defines If nonzero, the output will contain define-funs instead
 *                    of let bindings
 * 
 * \return a string in SMT-LIB v2 format for the formula represented by \a
 *         term, or NULL in case of errors. If not NULL, the returned string
 *         must be deallocated by the user with ::msat_free().
 */
char *msat_to_smtlib2_ext(msat_env e, msat_term term, const char *logic_name,
                          int use_defines);


/**
 * \brief Prints a single term in SMT-LIB v2 format
 *
 * Contrary to ::msat_to_smtlib2(), this function does not print symbol
 * declarations, and so it can be used to obtain a valid SMT-LIBv2
 * representation of the given \a term.
 *
 * \param The environment in which \a term is defined
 * \param term The term to print
 *
 * \return a string in SMT-LIB v2 format for the given \a term, or NULL in
 *         case of errors. If not NULL, the returned string must be
 *         deallocated by the user with ::msat_free().
 */
char *msat_to_smtlib2_term(msat_env e, msat_term term);


/**
 * \brief Dumps the given \a term in SMT-LIB v2 format to the given output file
 * 
 * \param e The environment in which \a term is defined
 * \param term The term to convert
 * \param logic_name Name of the SMT-LIBv2 logic for the output. Can be NULL
 * \param use_defines If nonzero, the output will contain define-funs instead
 *                    of let bindings
 * \param out The output file
 *                    
 * \return zero on success, nonzero on error.
 */
int msat_to_smtlib2_ext_file(msat_env e, msat_term term, const char *logic_name,
                             int use_defines, FILE *out);


/**
 * \brief Parses a list of named terms from a string in SMT-LIB v2 format.
 *
 * Given a string in SMT-LIB v2 format, collect and return all the terms with
 * a :named annotation.
 *
 * \param e Then environment in which terms are created
 * \param data The input string in SMT-LIBv2 format
 * 
 * \param out_n On success, the number of named terms is stored here. Must not
 *              be NULL.
 *
 * \param out_names On success, the names of the parsed terms are stored here.
 *                  Must not be NULL. Both the array and its elements are
 *                  dynamically allocated, and must be deallocated by the user
 *                  with ::msat_free()
 *
 * \param out_terms On success, the parsed named terms are stored here. Must
 *                  not be NULL. The array is dynamically allocated, and must
 *                  be deallocated by the user with ::msat_free()
 *
 * \return zero on success, nonzero on error.
 */
int msat_named_list_from_smtlib2(msat_env e, const char *data,
                                 size_t *out_n,
                                 char ***out_names, msat_term **out_terms);


/**
 * \brief Like ::msat_named_list_from_smtlib2(), but reads from a file instead
 * of a string.
 *
 * Given a FILE in SMT-LIB v2 format, collect and return all the terms with
 * a :named annotation.
 *
 * \param e Then environment in which terms are created
 * \param f The input file in SMT-LIBv2 format
 * 
 * \param out_n On success, the number of named terms is stored here. Must not
 *              be NULL.
 *
 * \param out_names On success, the names of the parsed terms are stored here.
 *                  Must not be NULL. Both the array and its elements are
 *                  dynamically allocated, and must be deallocated by the user
 *                  with ::msat_free()
 *
 * \param out_terms On success, the parsed named terms are stored here. Must
 *                  not be NULL. The array is dynamically allocated, and must
 *                  be deallocated by the user with ::msat_free()
 *
 * \return zero on success, nonzero on error.
 */
int msat_named_list_from_smtlib2_file(msat_env e, FILE *f,
                                      size_t *out_n,
                                      char ***out_names, msat_term **out_terms);

/**
 * \brief Converts the given list of named terms to SMT-LIB v2 format
 *
 * \param e The environment in which the terms are defined
 * \param n The number of terms/names to dump
 * \param names An array of names for the terms
 * \param terms The terms to convert
 *
 * \return a string in SMT-LIB v2 format storing all the named input terms, or
 *         NULL in case of errors. If not NULL, the returned string must be
 *         deallocated by the user with ::msat_free().
 */
char *msat_named_list_to_smtlib2(msat_env e, size_t n,
                                 const char **names, msat_term *terms);


/**
 * \brief Dumps the given list of named terms in SMT-LIB v2 format to the
 * given output file.
 *
 * \param e The environment in which the terms are defined
 * \param n The number of terms/names to dump
 * \param names An array of names for the terms
 * \param terms The terms to convert
 * \param out The output file
 *
 * \return zero on success, nonzero on error.
 */
int msat_named_list_to_smtlib2_file(msat_env e, size_t n,
                                    const char **names, msat_term *terms,
                                    FILE *out);


/**
 * \brief Parses a list of annotated terms from a string in SMT-LIB v2 format.
 *
 * Given a string in SMT-LIB v2 format, collect and return all and only the
 * terms with an annotation.
 *
 * \param e Then environment in which terms are created
 * \param data The input string in SMT-LIBv2 format
 * 
 * \param out_n On success, the number of terms is stored here. Must not be
 *              NULL. Notice that terms with multiple annotations are counted
 *              multiple times (see \a out_names below)
 *
 * \param out_terms On success, the parsed annotated terms are stored
 *                  here. Must not be NULL. The array is dynamically
 *                  allocated, and must be deallocated by the user with
 *                  ::msat_free(). If a term contains multiple annotations, it
 *                  will occur multiple times here (once for each annotation).
 *
 * \param out_annots On success, the annotations of the parsed terms are
 *                   stored here.  Must not be NULL. Both the array and its
 *                   elements are dynamically allocated, and must be
 *                   deallocated by the user with ::msat_free(). For each term
 *                   at index \a i in \a out_terms, the corresponding
 *                   annotation is stored as a key, value pair at indices \a
 *                   2*i and \a 2*i+1 in \a out_annots.
 *
 * \return zero on success, nonzero on error.
 */
int msat_annotated_list_from_smtlib2(msat_env e, const char *data,
                                     size_t *out_n, msat_term **out_terms,
                                     char ***out_annots);

/**
 * \brief Like ::msat_annotated_list_from_smtlib2(), but reads from a file
 * instead of a string.
 *
 * Given a FILE in SMT-LIB v2 format, collect and return all and only the
 * terms with an annotation.
 *
 * \param e Then environment in which terms are created
 * \param data The input string in SMT-LIBv2 format
 * 
 * \param out_n On success, the number of terms is stored here. Must not be
 *              NULL. Notice that terms with multiple annotations are counted
 *              multiple times (see \a out_names below)
 *
 * \param out_terms On success, the parsed annotated terms are stored
 *                  here. Must not be NULL. The array is dynamically
 *                  allocated, and must be deallocated by the user with
 *                  ::msat_free(). If a term contains multiple annotations, it
 *                  will occur multiple times here (once for each annotation).
 *
 * \param out_annots On success, the annotations of the parsed terms are
 *                   stored here.  Must not be NULL. Both the array and its
 *                   elements are dynamically allocated, and must be
 *                   deallocated by the user with ::msat_free(). For each term
 *                   at index \a i in \a out_terms, the corresponding
 *                   annotation is stored as a key, value pair at indices \a
 *                   2*i and \a 2*i+1 in \a out_annots.
 *
 * \return zero on success, nonzero on error.
 */
int msat_annotated_list_from_smtlib2_file(msat_env e, FILE *f,
                                          size_t *out_n, msat_term **out_terms,
                                          char ***out_annots);

/**
 * \brief Converts the given list of annotated terms to SMT-LIB v2 format
 *
 * \param e The environment in which the terms are defined
 * \param n The number of terms to dump
 * \param terms The terms to convert
 * \param annots An array of annotations for the terms. For each term at index
 *               \a i in \a terms, the corresponding (key, value) annotation
 *               is stored at indices \a 2*i and \a 2*i+1 in \a annots. Terms
 *               with multiple annotations should be listed multiple times in
 *               \a terms (once for each annotation).
 *
 * \return a string in SMT-LIB v2 format storing all the annotated input
 *         terms, or NULL in case of errors. If not NULL, the returned string
 *         must be deallocated by the user with ::msat_free().
 */
char *msat_annotated_list_to_smtlib2(msat_env e, size_t n,
                                     msat_term *terms, const char **annots);

/**
 * \brief Like ::msat_annotated_list_to_smtlib2(), but writes to a FILE
 * instead of returning a string.
 *
 * \param e The environment in which the terms are defined
 * \param n The number of terms to dump
 * \param terms The terms to convert
 * \param annots An array of annotations for the terms. For each term at index
 *               \a i in \a terms, the corresponding (key, value) annotation
 *               is stored at indices \a 2*i and \a 2*i+1 in \a annots. Terms
 *               with multiple annotations should be listed multiple times in
 *               \a terms (once for each annotation).
 * \param out The output file
 *
 * \return zero on success, nonzero on error.
 */
int msat_annotated_list_to_smtlib2_file(msat_env e, size_t n,
                                        msat_term *terms, const char **annots,
                                        FILE *out);

/*@}*/ /* end of Term parsing/printing group */

/**
 * \name Problem solving
 */

/*@{*/

/**
 * \brief Pushes a checkpoint for backtracking in an environment
 *
 * \param e The environment in which to operate
 * \return zero on success, nonzero on error
 */
int msat_push_backtrack_point(msat_env e);

/**
 * \brief Backtracks to the last checkpoint set in the environment \a e
 *
 * \param e The environment in which to operate
 * \return zero on success, nonzero on error
 */
int msat_pop_backtrack_point(msat_env e);

/**
 * \brief returns the number of backtrack points in the given environment
 */
size_t msat_num_backtrack_points(msat_env e);

/**
 * \brief Resets an environment.
 *
 * Clears the assertion stack (see ::msat_assert_formula,
 * ::msat_push_backtrack_point, ::msat_pop_backtrack_point) of \a e.
 * However, terms created in \a e are still valid.
 * 
 * \param e The environment to reset
 * \return zero on success, nonzero on error
 */
int msat_reset_env(msat_env e);

/**
 * \brief Adds a logical formula to an environment
 * \param e The environment in which the formula is asserted
 * \param formula The formula to assert. Must have been created in \a e,
 *        otherwise bad things will happen (probably a crash)
 * \return zero on success, nonzero on error
 */
int msat_assert_formula(msat_env e, msat_term formula);

/**
 * \brief Adds a Boolean variable at the end of the list of preferred
 *        variables for branching when solving the problem
 *
 * \param e The environment in which to operate
 * \param boolvar The Boolean variable to add to the preferred list
 * \param phase The phase of the variable for branching. If MSAT_UNDEF,
 *              the phase is determined by the currently configured heuristics
 * \return zero on success, nonzero on error
 */
int msat_add_preferred_for_branching(msat_env e, msat_term boolvar,
                                     msat_truth_value phase);

/**
 * \brief Clears the list of preferred variables for branching
 *
 * \param e The environment in which to operate
 * \return zero on success, nonzero on error
 */
int msat_clear_preferred_for_branching(msat_env e);

/**
 * \brief Checks the satiafiability of the given environment.
 *
 * Checks the satisfiability of the conjunction of all the formulas asserted
 * in \a e (see ::msat_assert_formula). Before calling this function, the
 * right theory solvers must have been enabled (see ::msat_add_theory).
 *
 * \param e The environment to check.
 * \return ::MSAT_SAT if the problem is satisfiable, ::MSAT_UNSAT if it is
 *         unsatisfiable, and ::MSAT_UNKNOWN if there was some error or if
 *         the satisfiability can't be determined.
 */
msat_result msat_solve(msat_env e);

/**
 * \brief Checks the satiafiability of the given environment
 *        under the given assumptions
 *
 * Checks the satisfiability of the conjunction of all the formulas asserted
 * in \a e (see ::msat_assert_formula), plus the conjunction of the given
 * assumptions, which can only be (negated) Boolean constants.
 * If ::MSAT_UNSAT is returned, the function ::msat_get_unsat_assumptions()
 * can be used to retrieve the list of assumptions responsible for the
 * inconsistency.
 *
 * \param e The environment to check.
 * \param assumptions The list of assumptions. Can only be (negated) Boolean
 *                    constants
 * \param num_assumptions The number of assumptions.
 * \return ::MSAT_SAT if the problem is satisfiable, ::MSAT_UNSAT if it is
 *         unsatisfiable, and ::MSAT_UNKNOWN if there was some error or if
 *         the satisfiability can't be determined.
 */
msat_result msat_solve_with_assumptions(msat_env e, msat_term *assumptions,
                                        size_t num_assumptions);
                                        

/**
 * \brief Performs AllSat over the \a important atoms of the conjunction
 * of all formulas asserted in \a e (see ::msat_assert_formula). When used
 * in incremental mode, a backtrack point should be pushed before calling this
 * function, and popped after this call has completed. Not doing this changes
 * the satisfiability of the formula.
 *
 * \param e The environment to use
 * \param important An array of important atoms. If NULL, all atoms are
 *                  considered important
 * \param num_important The size of the \a important array. If \a important is
 *                      NULL, set this to zero
 * \param func The callback function to be notified about models found (see
 *             ::msat_all_sat_model_callback). Cannot be NULL
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted
 * \return The number of models found, or -1 on error.
 *         If the solver detects that the formula is a tautology,
 *         -2 is returned. Note however that:
 *
 *         1. not all tautologies are detected by the solver. I.e., sometimes
 *            the solver will explicitly enumerate all the models of the
 *            formula even for tautologies
 *
 *         2. the number returned might be an over-approximation of the actual
 *            number of models. This can happen because the solver might
 *            sometimes report the same model more than once. In these cases,
 *            the callback function will be called multiple times with the
 *            same input.
 */
int msat_all_sat(msat_env e, msat_term *important, size_t num_important,
                 msat_all_sat_model_callback func, void *user_data);

/**
 * \brief Enumerates diverse models over the asserted stack.
 *
 * Can only be called when model generation is on and proof generation is off.
 * 
 * Notice that this function changes the asserted formula in order to generate
 * the diverse models, by adding clauses based on the diversifiers. When used
 * in incremental mode a backtrack point should be pushed before calling this
 * function, and popped after this call has completed. Not doing this changes
 * the satisfiability of the formula.
 * 
 * \param e The environment to use
 * \param diversifiers the terms over which to diversify. On each
 *        succesive model, at least one of these terms will have a different
 *        value.
 * \param num_diversifiers the size of the \a diversifiers array.
 * \param func The callback function to be notified about models found (see
 *             ::msat_solve_diversify_model_callback). Cannot be NULL.
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted
 *                  
 * \return The number of models found, or -1 on error.
 *         (If the formula is unsat, 0 is returned).
 */
int msat_solve_diversify(msat_env e,
                         msat_term *diversifiers, size_t num_diversifiers,
                         msat_solve_diversify_model_callback func,
                         void *user_data);

/**
 * \brief Returns the list of formulas in the assertion stack.
 *
 * The return value is a dynamically-allocated array of *num_asserted
 * elements, which must be deallocated by the user. NULL is returned in case of
 * errors. The array elements are formulas that are logically equivalent to
 * the one asserted using ::msat_assert_formula
 *
 * \param e The environment in which to operate.
 * \param num_asserted Pointer to a valid address for storing the number
 *                     of formulas currently in the assertion stack.
 *                     
 * \return An array with the asserted formulas, or NULL in case of errors.
 *         The array is must be deallocated by allocated the user with
 *         ::msat_free().
 */
msat_term *msat_get_asserted_formulas(msat_env e, size_t *num_asserted);

/**
 * \brief Retrieves the theory lemmas used in the last search (see
 *        ::msat_solve).
 *
 * For the function to work, the option "dpll.store_tlemmas" must be set to
 * "true" in the configuration object for the environment.
 *        
 * \param e The environment in which to operate.
 * \param num_tlemmas Pointer to a valid address for storing the number
 *                    of theory lemmas returned.
 *                    
 * \return An array with the theory lemmas, or NULL in case of errors.
 *         The array must be deallocated by the user with ::msat_free().
 */
msat_term *msat_get_theory_lemmas(msat_env e, size_t *num_tlemmas);


/**
 * \brief Returns a string with search statistics for the given environment.
 *
 * The returned string will contain newline-separated statistics for the DPLL
 * engine and the active theory solvers in the given environment.
 *
 * \param e The environment in which to operate.
 * \return A string with search statistics, or NULL in case of errors.
 *         The string must be deallocated by the user with ::msat_free(). 
 */
char *msat_get_search_stats(msat_env e);

/**
 * \brief Simplify the input formula by performing variable elimination with
 *        toplevel equalities.
 *
 * Apply rewriting and "toplevel propagation", i.e. inlining of toplevel
 * equalities, until a fixpoint is reached. The constants occurring in \a
 * to_protect will not be eliminated. If \a to_protect is NULL, only rewriting
 * is performed.
 *
 * \param e The environment in which to operate.
 * \param formula The formula to simplify.
 * \param to_protect The constants that should never be eliminated.
 * \param num_to_protect The size of the \a to_protect array.
 *
 * \return The simplified formula, or a t s.t. ::MSAT_ERROR_TERM(t) is true in
 *         case of errors
 */
msat_term msat_simplify(msat_env e, msat_term formula,
                        msat_term *to_protect, size_t num_to_protect);


/*@}*/ /* end of Problem solving group */

/**
 * \name Interpolation
 */
/*@{*/

/**
 * \brief Creates a new group for interpolation.
 *
 * When computing an interpolant, formulas are organized into several groups,
 * which are partitioned into two sets GA and GB. The conjuction of formulas
 * in GA will play the role of A, and that of formulas in GB will play the
 * role of B (see ::msat_set_itp_group, ::msat_get_interpolant).
 *
 * \param e The environment in which to operate.
 * \return an identifier for the new group, or -1 in case of error.
 */
int msat_create_itp_group(msat_env e);

/**
 * \brief Sets the current interpolation group.
 *
 * All the formulas asserted after this call (with ::msat_assert_formula) will
 * belong to \a group.
 *
 * \param e The environment in which to operate.
 * \param group The group. Must have been previously created with
 *        ::msat_create_itp_group.
 * \return zero on success, nonzero on error.
 */ 
int msat_set_itp_group(msat_env e, int group);

/**
 * \brief Computes an interpolant for a pair (A, B) of formulas.
 *
 * A is the conjucntion of all the assumed formulas in the \a groups_of_a
 * groups (see ::msat_create_itp_group), and B is the rest of assumed
 * formulas.
 *
 * This function must be called only after ::msat_solve, and only if
 * MSAT_UNSAT was returned. Moreover, interpolation must have been enabled in
 * the configuration for the environment
 *
 * \param e The environment in which to operate.
 * \param groups_of_a An array of group identifiers.
 * \param n The size of the \a groups_of_a array.
 * \return The interpolating term, or a t s.t. MSAT_ERROR_TERM(t) is true in
 *         case of errors.
 */
msat_term msat_get_interpolant(msat_env e, int *groups_of_a, size_t n);

/*@}*/ /* end of interpolation group */


/**
 * \name Model Computation
 */
/*@{*/

/**
 * \brief Returns the value of the term \a term in the current model
 *
 * Preconditions:
 * - model computation was enabled in the configuration of the environment
 * - the last call to ::msat_solve returned a ::MSAT_SAT result
 * - no assert/push/pop/allsat commands have been issued in the meantime
 * 
 * \param e The environment in use
 * \param term The term of interest.
 * \return The model value for \a term. If an error occurs, the return value
 *         \a ret is such that MSAT_ERROR_TERM(ret) is true
 */
msat_term msat_get_model_value(msat_env e, msat_term term);

/**
 * \brief Creates a model iterator
 * \param e The environment in use
 * \return an iterator for the current model
 */
msat_model_iterator msat_create_model_iterator(msat_env e);

/**
 * \brief Checks whether \a i can be incremented
 * \param i A model iterator
 * \return nonzero if \a i can be incremented, zero otherwise
 */
int msat_model_iterator_has_next(msat_model_iterator i);

/**
 * \brief Returns the next (term, value) pair in the model, and increments the
 *        given iterator.
 * \param i The model iterator to increment.
 * \param t Output value for the next variable/function call in the model.
 * \param v Output value for the next value in the model.
 * \return nonzero in case of error.
 */
int msat_model_iterator_next(msat_model_iterator i, msat_term *t, msat_term *v);

/**
 * \brief Destroys a model iterator.
 * \param i The iterator to destroy.
 */
void msat_destroy_model_iterator(msat_model_iterator i);

/**
 * \brief Creates a model object.
 * \param e The environment in use.
 * \return A model object. Use MSAT_ERROR_MODEL() to check for errors.
 */
msat_model msat_get_model(msat_env e);

/**
 * \brief Destroys the given model object.
 *
 * \param m A model object.
 */
void msat_destroy_model(msat_model m);

/**
 * \brief Evaluates the input term in the given model.
 *
 * \param m The model used for the evaluation.
 * \param t The term to evaluate.
 * \return the value for \a t in \a m. Use MSAT_ERROR_TERM() to check
 *         for errors.
 */
msat_term msat_model_eval(msat_model m, msat_term t);

/**
 * \brief Creates an iterator for the given model.
 *
 * \param m The model to iterate.
 * \return A model iterator. Use MSAT_ERROR_MODEL_ITERATOR() to check
 *         for errors.
 */
msat_model_iterator msat_model_create_iterator(msat_model m);

/*@}*/ /* end of model computation group */

/**
 * \name Unsat Core Computation
 */
/*@{*/

/**
 * \brief Returns the unsatisfiable core of the last search (see ::msat_solve)
 *        as a subset of the asserted formulas, if the problem was
 *        unsatisfiable.
 *
 * \param e The environment in which to operate.
 * \param core_size Pointer to a valid address for storing the number
 *                  of formulas in the unsat core.
 * \return An array with the unsat core, or NULL in case of errors.
 *         The array must be deallocated by the user with ::msat_free().
 */
msat_term *msat_get_unsat_core(msat_env e, size_t *core_size);

/**
 * \brief Returns the unsatisfiable core of the last search (see ::msat_solve)
 *        as a subset of the asserted formulas, computed using an external
 *        Boolean unsat core extractor (see ::msat_ext_unsat_core_extractor).
 *
 * \param e The environment in which to operate.
 * \param core_size Pointer to a valid address for storing the number of
 *                  formulas in the unsat core.
 * \param extractor The external Boolean core extractor.
 * \param user_data Generic data pointer which will be passed to \a extractor.
 *                  Can be anything, its value will not be interpreted.
 * \return An array with the unsat core, or NULL in case of errors.
 *         The array must be deallocated by the user with ::msat_free().
 */
msat_term *msat_get_unsat_core_ext(msat_env e, size_t *core_size,
                                   msat_ext_unsat_core_extractor extractor,
                                   void *user_data);


/**
 * \brief Returns the list of assumptions resposible for the unsatisfiability
 * detected by the last search (see ::msat_solve_with_assumptions).
 *
 * \param e The environment in which to operate.
 * \param assumps_size Pointer to a valid address for storing the number
 *                     of formulas in the returned array.
 *                     
 * \return An array with the list of inconsistent assumptions, or NULL in case
 *         of errors. The array must be deallocated by the user with
 *         ::msat_free().
 */
msat_term *msat_get_unsat_assumptions(msat_env e, size_t *assumps_size);

/**
 * \brief Returns a proof manager for the given environment.
 *
 * The manager must be destroyed by the user, with ::msat_destroy_proof_manager.
 * In order to obtain a non-error result, the option "proof_generation" must
 * be set to "true" in the configuration used for creating the environment.
 *
 * \param e The environment in which to operate.
 * 
 * \return A proof manager for the environment. MSAT_ERROR_PROOF_MANAGER can
 *         be used to check whether an error occurred.
 */
msat_proof_manager msat_get_proof_manager(msat_env e);

/**
 * \brief Destroys a proof manager.
 *
 * Destroying a proof manager will also destroy all the proofs associated with
 * it.
 * 
 * \param m The proof manager to destroy.
 */
void msat_destroy_proof_manager(msat_proof_manager m);

/**
 * \brief Returns a proof of unsatisfiability.
 *
 * a proof is recursively defined as:
 *
 *   msat_proof ::= msat_term
 *               |  name msat_proof*
 * 
 * i.e., it is either a term or a list of a name and children proofs.
 * Proofs can be distinguished by their name, or by whether they are
 * terms. Relevant proofs include:
 * 
 * "clause-hyp", which are the clauses of the (CNF conversion of the) input
 * problem. They have a list of terms as children
 * 
 * "res-chain", representing Boolean resolution chains. The children are an
 * interleaving of proofs and terms, where terms are the pivots for the
 * resolution. For example:
 *    "res-chain p1 v p2" represents a resolution step between p1 and p2 on
 *    the pivot v
 * 
 * "theory-lemma", representing theory lemmas. They have as
 * children a list of terms that consititute the lemma, plus an optional
 * last element which is a more detailed proof produced by a theory solver.
 *
 * \param m The proof manager in which to operate.
 * 
 * \return The proof of unsatisfiability associated to the latest
 *         ::msat_solve() call, or an object p s.t. MSAT_ERROR_PROOF(p) is
 *         true in case of errors.
 */
msat_proof msat_get_proof(msat_proof_manager m);

/**
 * \brief Returns a numeric identifier for \a p
 *
 * The returned value is guaranteed to be unique within the proof manager in
 * which \a p was defined. Therefore, it can be used to test two proofs for
 * equality, as well as a hash value.
 *
 * \param p A proof. 
 * \return a unique (within the defining manager) numeric identifier
 */
size_t msat_proof_id(msat_proof p);

/**
 * \brief Checks whether a proof object is a term.
 *
 * \param p The proof to test.
 *
 * \return nonzero if \a p is a term proof, zero otherwise.
 */ 
int msat_proof_is_term(msat_proof p);

/**
 * \brief Retrieves the term associated to a term proof.
 *
 * \param p The proof from which to get the term. Must be a term proof.
 *
 * \return The term associated with the input proof.
 */
msat_term msat_proof_get_term(msat_proof p);

/**
 * \brief Retrieves the name of a non-term proof.
 *
 * \param p A non-term proof.
 *
 * \return The name of the given proof.
 */
const char *msat_proof_get_name(msat_proof p);

/**
 * \brief Retrieves the number of children of a non-term proof.
 *
 * \param p A non-term proof.
 *
 * \return The arity of the given proof.
 */
size_t msat_proof_get_arity(msat_proof p);

/**
 * \brief Retrieves a sub-proof of a given proof.
 *
 * \param p A non-term proof.
 * \param i The index of the child proof to retrieve.
 *
 * \return a Child proof of the given proof.
 */
msat_proof msat_proof_get_child(msat_proof p, size_t i);

/*@}*/ /* end of unsat core computation group */

/**
 * \name External SAT Solver Interface
 */
/*@{*/

/**
 * \brief Callback object for using an external SAT solver as DPLL engine in
 * MathSAT.
 */
typedef struct msat_dpll_callback { void *repr; } msat_dpll_callback;

/**
 * \brief Interface that external SAT solvers must implement.
 */
typedef struct msat_ext_dpll_interface {
    /**
     * \brief Creates a new variable in the SAT solver.
     * \param self Pointer to the SAT solver.
     * \return the DIMACS index of the new variable, or -1 in case of errors.
     */
    int (*new_var)(void *self);
    
    /**
     * \brief Marks a variable as a decision variable.
     * \param self Pointer to the SAT solver.
     * \param var the DIMACS index for the variable.
     * \param yes decision flag.
     * \return zero on success, nonzero on error.
     */
    int (*set_decision_var)(void *self, int var, int yes);

    /**
     * \brief Sets the frozen status of a variable.
     * \param self Pointer to the SAT solver.
     * \param var the DIMACS index for the variable.
     * \param yes frozen flag.
     * \return zero on success, nonzero on error.
     */
    int (*set_frozen)(void *self, int var, int yes);

    /**
     * \brief Adds a clause to the SAT solver.
     * \param self Pointer to the SAT solver.
     * \param clause array of literals in DIMACS format, terminated by 0.
     * \param permanent If nonzero, the clause is meant to be permanent.
     * \param during_callback If nonzero, the function is called by one of the
     *                        ::msat_dpll_callback methods
     * \return zero on success, nonzero on error
     */
    int (*add_clause)(void *self,
                      int *clause, int permanent, int during_callback);

    /**
     * \brief Checks the satisfiability (possibly under assumptions)
     *        of the list of added clauses.
     * \param self Pointer to the SAT solver.
     * \param assumptions array of literals in DIMACS format, terminated by 0.
     * \param out_conflicting_assumptions if the problem is unsatisfiable,
     *                                    this pointer should be set to a
     *                                    (zero-terminated) list of the
     *                                    assumptions responsible for the
     *                                    unsatisfiability. The solver should
     *                                    use its own internal storage for the
     *                                    array.
     * \return ::MSAT_SAT if the problem is satisfiable,
     *         ::MSAT_UNSAT if it is unsat, or ::MSAT_UNKNOWN in case of errors.
     */    
    msat_result (*solve)(void *self, int *assumptions,
                         int **out_conflicting_assumptions);

    /**
     * \brief Retrieves the model value for the given literal
     * \param self Pointer to the SAT solver.
     * \param lit literal in DIMACS format.
     * \return The truth value for the literal.
     */
    msat_truth_value (*model_value)(void *self, int lit);

    /**
     * \brief Adds a (theory-deduced) literal to the current trail.
     * \param self Pointer to the SAT solver.
     * \param lit literal in DIMACS format.
     * \return zero on success, nonzero on error.
     */
    int (*enqueue_assignment)(void *self, int lit);

    /**
     * \brief Tells the solver to delete all the clauses containing the given
     *        variable.
     * \param self Pointer to the SAT solver.
     * \param var variable in DIMACS format.
     * \return zero on success, nonzero on error.
     */
    int (*remove_clauses_containing)(void *self, int var);
    
    /**
     * \brief Completely resets the state of the solver.
     * \param self Pointer to the SAT solver.
     * \return zero on success, nonzero on error.
     */
    int (*reset)(void *self);

    /**
     * \brief Associates to the solver a callback object for interacting with
     *        MathSAT.
     * \param self Pointer to the SAT solver.
     * \param cb The ::msat_dpll_callback object.
     * \return zero on success, nonzero on error.
     */
    int (*set_callback)(void *self, msat_dpll_callback cb);
} msat_ext_dpll_interface;

/**
 * \brief Sets an external dpll engine to be used by an environment
 * \param env The environment in which to operate.
 * \param engine The engine to use
 * \return zero on success, nonzero on error
 */
int msat_set_external_dpll_engine(msat_env env,
                                  msat_ext_dpll_interface *engine);

/**
 * \brief Callback function that the external SAT solver must call when a
 *        round of BCP has been completed without finding a Boolean conflict.
 *
 * The \a code value set by callback function tells the SAT solver what to do.
 *  - if it is ::MSAT_TRUE, the SAT solver can go on.
 * 
 *  - if it is ::MSAT_FALSE, MathSAT found a theory conflict, which is
 *    stored in \a conflict. The SAT solver is expected to perform conflict
 *    analysis on it and backjump.
 *
 *  - if it is ::MSAT_UNDEF, the SAT solver needs to perform another
 *    round of BCP, because MathSAT enqueued some new literals on the trail.
 *
 * \param cb The callback object to use.
 * \param code Pointer to a variable set by the callback function.
 * \param conflict Pointer for retrieving the theory conflict,
 *        when the \a code value is set to ::MSAT_FALSE.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_no_conflict_after_bcp(msat_dpll_callback cb,
                                             msat_truth_value *code,
                                             int **conflict);

/**
 * \brief Callback function that the external SAT solver must call when a
 *        Boolean model has been found.
 *
 * The \a code value set by callback function tells the SAT solver what to do.
 *  - if it is ::MSAT_TRUE, the model is theory satisfiable,
 *    so the formula is satisfiable.
 * 
 *  - if it is ::MSAT_FALSE, MathSAT found a theory conflict, which is
 *    stored in \a conflict. The SAT solver is expected to perform conflict
 *    analysis on it and backjump.
 *
 *  - if it is ::MSAT_UNDEF, MathSAT created some new variables
 *    that need to be assigned by the SAT solver, so the search should continue.
 *
 * \param cb The callback object to use.
 * \param code Pointer to a variable set by the callback function.
 * \param conflict Pointer for retrieving the theory conflict,
 *        when the \a code value is set to ::MSAT_FALSE.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_model_found(msat_dpll_callback cb,
                                   msat_truth_value *code, int **conflict);

/**
 * \brief Callback function that the external SAT solver must call whenever
 *        a literal is added to the trail.
 *
 * \param cb The callback object to use.
 * \param lit The assigned literal in DIMACS format.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_notify_assignment(msat_dpll_callback cb, int lit);

/**
 * \brief Callback function that the external SAT solver must call whenever
 *        a new decision level is opened.
 *
 * \param cb The callback object to use.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_notify_new_level(msat_dpll_callback cb);

/**
 * \brief Callback function that the external SAT solver must call whenever
 *        it backtracks.
 *
 * \param cb The callback object to use.
 * \param level The target decision level for backtracking.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_notify_backtrack(msat_dpll_callback cb, int level);

/**
 * \brief Callback function that the external SAT solver must call for asking
 *        MathSAT the reason for a theory-deduced literal, during conflict
 *        analysis.
 *
 * \param cb The callback object to use.
 * \param level The literal whose reason needs to be computed.
 * \param reason Pointer to the zero-terminated reason clause for \a lit, with
 *               the first element being \a lit itself.
 * \return zero on success, nonzero on error.
 */
int msat_dpll_callback_ask_theory_reason(msat_dpll_callback cb,
                                         int lit, int **reason);

/*@}*/ /* end of external sat solver interface group */

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* MSAT_MATHSAT_H_INCLUDED */
