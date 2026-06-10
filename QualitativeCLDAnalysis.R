############################################################
# Structural analysis of a qualitative CLD
#
# Input:
#   - Vensim .mdl file containing the finalized causal loop diagram
#
# Output:
#   - CSV files supporting feedback-loop analysis and path-based
#     qualitative influence analysis
#
# Notes:
#   - This script does not estimate parameters or simulate dynamics.
#   - It does not compute inverse-based Levins community effects.
#   - No diagonal self-effects are imposed.
############################################################

# ==========================================================
# 1. User settings
# ==========================================================

mdl_path <- "data/CLD-final.mdl"   # Specify the path to the Vensim .mdl file
out_dir  <- "outputs"              # Specify the folder where output CSV files will be saved

target_var <- "30-Day Readmission Rate"
max_loop_length <- 16

# Full first-arrival simple paths can be computationally expensive for large and complicated CLDs.
# For the finalized CLD this should usually be feasible. If needed,
# replace vcount(g) - 1L later with a smaller value such as 16L.
path_cutoff_user <- NULL


# ==========================================================
# 2. Required Packages
# ==========================================================
if (!requireNamespace("igraph", quietly = TRUE)) install.packages("igraph")
library(igraph)

# ==========================================================
# 3. Utility functions
# ==========================================================

write_output_csv <- function(x, filename) {
  write.csv(
    x,
    file = file.path(out_dir, filename),
    row.names = FALSE,
    na = "",
    fileEncoding = "UTF-8"
  )
}

replace_numeric_na <- function(df, value = 0) {
  numeric_cols <- vapply(df, is.numeric, logical(1))
  df[numeric_cols] <- lapply(df[numeric_cols], function(x) {
    x[is.na(x)] <- value
    x
  })
  df
}

collapse_values <- function(x) {
  x <- sort(unique(x))
  if (length(x) == 0) "" else paste(x, collapse = "; ")
}

# ==========================================================
# 4. Read Vensim model and isolate the sketch section
# ==========================================================

mdl_txt <- readLines(mdl_path, encoding = "UTF-8", warn = FALSE)

sketch_start <- grep("Sketch information", mdl_txt, fixed = TRUE)[1]

if (is.na(sketch_start)) {
  stop("The Vensim sketch section was not found in the .mdl file.")
}

sketch_txt <- mdl_txt[sketch_start:length(mdl_txt)]


# ==========================================================
# 5. Extract variables and signed causal links
# ==========================================================

node_lines <- sketch_txt[grepl("^10,", sketch_txt)]
node_parts <- strsplit(node_lines, ",", fixed = TRUE)

nodes <- data.frame(
  id = as.integer(vapply(node_parts, `[`, character(1), 2)),
  name = trimws(gsub('^"|"$', "", vapply(node_parts, `[`, character(1), 3))),
  stringsAsFactors = FALSE
)

link_lines <- sketch_txt[grepl("^1,", sketch_txt)]
link_parts <- strsplit(link_lines, ",", fixed = TRUE)

links_raw <- data.frame(
  from_id = as.integer(vapply(link_parts, `[`, character(1), 3)),
  to_id   = as.integer(vapply(link_parts, `[`, character(1), 4)),
  code    = as.integer(vapply(link_parts, `[`, character(1), 7)),
  stringsAsFactors = FALSE
)

# Vensim polarity codes observed in the finalized model:
#   43 = positive causal link
#   45 = negative causal link
links_raw$sign <- ifelse(
  links_raw$code == 43, 1L,
  ifelse(links_raw$code == 45, -1L, NA_integer_)
)

id_to_name <- setNames(nodes$name, nodes$id)

links_named <- data.frame(
  from = unname(id_to_name[as.character(links_raw$from_id)]),
  to   = unname(id_to_name[as.character(links_raw$to_id)]),
  code = links_raw$code,
  sign = links_raw$sign,
  stringsAsFactors = FALSE
)

links_named <- links_named[
  !is.na(links_named$from) &
    !is.na(links_named$to) &
    !is.na(links_named$sign),
]

edges <- unique(links_named[, c("from", "to", "sign")])
edges$polarity <- ifelse(edges$sign == 1L, "positive", "negative")

if (nrow(edges) == 0) {
  stop("No signed causal links were extracted from the model.")
}


# ==========================================================
# 6. Validation checks
# ==========================================================

conflicts <- aggregate(
  sign ~ from + to,
  data = edges,
  FUN = function(x) length(unique(x))
)

conflicts <- conflicts[conflicts$sign > 1, ]

self_links <- edges[edges$from == edges$to, ]

unknown_codes <- sort(unique(links_raw$code[is.na(links_raw$sign)]))

duplicate_variable_names <- sort(unique(nodes$name[duplicated(nodes$name)]))

if (nrow(conflicts) > 0) {
  stop(
    "Conflicting duplicate causal links were found. ",
    "Inspect source-target pairs with different signs before continuing."
  )
}

if (length(unknown_codes) > 0) {
  warning(
    "Some Vensim link polarity codes were not recognized and were excluded: ",
    paste(unknown_codes, collapse = ", ")
  )
}
# ==========================================================
# 7. Build signed directed graph
# ==========================================================

g <- graph_from_data_frame(edges, directed = TRUE)

vars <- sort(V(g)$name)

if (!(target_var %in% vars)) {
  stop(paste0("Target variable not found in the graph: ", target_var))
}

scc <- components(g, mode = "strong")
core_id <- which.max(scc$csize)

feedback_core_vars <- sort(
  names(scc$membership[scc$membership == core_id])
)
# ==========================================================
# 8. Enumerate and classify simple directed feedback loops
# ==========================================================

cat("\nEnumerating simple directed feedback loops...\n")
cat("  Maximum loop length:", max_loop_length, "links\n")

# This function enumerates simple directed cycles in the signed CLD.
# A simple cycle does not repeat variables within the same loop.
# The max_len argument limits the maximum number of variables in a loop.
#
# The implementation follows a Johnson-style depth-first search logic
# and is used here for transparent reconstruction of feedback loops from
# the exported Vensim network.

johnson_cycles <- function(g, max_len = 16) {
  if (!igraph::is_directed(g)) {
    stop("The graph must be directed.")
  }
  
  if (is.null(V(g)$name)) {
    V(g)$name <- as.character(seq_len(vcount(g)))
  }
  
  adj <- adjacent_vertices(g, V(g), mode = "out")
  adj <- lapply(adj, as.integer)
  
  n <- vcount(g)
  cycles <- list()
  blocked <- rep(FALSE, n)
  B <- vector("list", n)
  stack <- integer(0)
  
  unblock <- function(u) {
    blocked[u] <<- FALSE
    
    while (length(B[[u]]) > 0) {
      w <- B[[u]][1]
      B[[u]] <<- B[[u]][-1]
      
      if (blocked[w]) {
        unblock(w)
      }
    }
  }
  
  circuit <- function(v, s, allowed) {
    found_cycle <- FALSE
    blocked[v] <<- TRUE
    stack <<- c(stack, v)
    
    if (length(stack) <= max_len) {
      for (w in adj[[v]]) {
        if (!allowed[w]) next
        
        if (w == s) {
          cycles[[length(cycles) + 1]] <<- stack
          found_cycle <- TRUE
        } else if (!blocked[w]) {
          if (circuit(w, s, allowed)) {
            found_cycle <- TRUE
          }
        }
      }
    }
    
    if (found_cycle) {
      unblock(v)
    } else {
      for (w in adj[[v]]) {
        if (!allowed[w]) next
        
        if (!(v %in% B[[w]])) {
          B[[w]] <<- c(B[[w]], v)
        }
      }
    }
    
    stack <<- stack[-length(stack)]
    
    found_cycle
  }
  
  for (s in seq_len(n)) {
    allowed <- rep(FALSE, n)
    allowed[s:n] <- TRUE
    
    blocked[allowed] <- FALSE
    
    for (i in which(allowed)) {
      B[[i]] <- integer(0)
    }
    
    stack <- integer(0)
    circuit(s, s, allowed)
  }
  
  lapply(cycles, function(cycle_ids) V(g)$name[cycle_ids])
}


# Classify loop polarity.
# A loop is reinforcing if the product of its causal-link signs is positive.
# A loop is balancing if the product of its causal-link signs is negative.

loop_sign <- function(g, cycle_names) {
  from <- cycle_names
  to <- c(cycle_names[-1], cycle_names[1])
  
  edge_ids <- mapply(
    function(a, b) igraph::get_edge_ids(g, c(a, b), directed = TRUE),
    from,
    to
  )
  
  if (any(edge_ids == 0)) {
    stop("A cycle contains an edge that was not found in the graph.")
  }
  
  as.integer(prod(E(g)$sign[edge_ids]))
}


cycles <- johnson_cycles(g, max_len = max_loop_length)

loop_df <- data.frame(
  loop_id = seq_along(cycles),
  loop = vapply(cycles, function(x) paste(x, collapse = " -> "), character(1)),
  length = vapply(cycles, length, integer(1)),
  sign = vapply(cycles, function(x) loop_sign(g, x), integer(1)),
  stringsAsFactors = FALSE
)

loop_df$polarity <- ifelse(loop_df$sign == 1L, "reinforcing", "balancing")

loop_df$length_bin <- cut(
  loop_df$length,
  breaks = c(0, 4, 8, max_loop_length),
  labels = c("short_leq_4", "medium_5_to_8", "long_9_to_16"),
  right = TRUE
)

loop_df <- loop_df[order(loop_df$length, -loop_df$sign, loop_df$loop), ]
loop_df$loop_id <- seq_len(nrow(loop_df))

cat("  Total simple feedback loops:", nrow(loop_df), "\n")
cat("  Reinforcing loops:", sum(loop_df$sign == 1L), "\n")
cat("  Balancing loops:", sum(loop_df$sign == -1L), "\n")
cat("  Loops including target variable:",
    sum(grepl(target_var, loop_df$loop, fixed = TRUE)), "\n")
# ==========================================================
# 9. Summarise variable participation in feedback loops
# ==========================================================

cat("\nSummarising variable participation in feedback loops...\n")

# This section counts how often each variable appears in the
# reconstructed feedback loops. Participation is reported separately
# for reinforcing and balancing loops.
#
# These counts are structural descriptors of the CLD. They should not
# be interpreted as statistical importance, causal effect size, or
# intervention priority by themselves.

if (nrow(loop_df) > 0) {
  
  loop_incidence <- data.frame(
    loop_id = rep(loop_df$loop_id, times = loop_df$length),
    variable = unlist(strsplit(loop_df$loop, " -> ", fixed = TRUE), use.names = FALSE),
    stringsAsFactors = FALSE
  )
  
  loop_incidence <- merge(
    loop_incidence,
    loop_df[, c("loop_id", "length", "sign", "polarity", "length_bin")],
    by = "loop_id",
    all.x = TRUE
  )
  
  total_participation <- aggregate(
    loop_id ~ variable,
    loop_incidence,
    function(x) length(unique(x))
  )
  names(total_participation)[2] <- "n_loops_total"
  
  reinforcing_participation <- aggregate(
    loop_id ~ variable,
    loop_incidence[loop_incidence$sign == 1L, ],
    function(x) length(unique(x))
  )
  names(reinforcing_participation)[2] <- "n_reinforcing"
  
  balancing_participation <- aggregate(
    loop_id ~ variable,
    loop_incidence[loop_incidence$sign == -1L, ],
    function(x) length(unique(x))
  )
  names(balancing_participation)[2] <- "n_balancing"
  
  variable_participation <- Reduce(
    function(x, y) merge(x, y, by = "variable", all = TRUE),
    list(total_participation, reinforcing_participation, balancing_participation)
  )
  
  variable_participation <- replace_numeric_na(variable_participation, 0)
  
  variable_participation$share_reinforcing <-
    variable_participation$n_reinforcing / variable_participation$n_loops_total
  
  variable_participation$share_balancing <-
    variable_participation$n_balancing / variable_participation$n_loops_total
  
  variable_participation <- variable_participation[
    order(
      -variable_participation$n_loops_total,
      -variable_participation$n_reinforcing,
      variable_participation$variable
    ),
  ]
  
} else {
  
  warning("No feedback loops were found. Variable participation table is empty.")
  
  variable_participation <- data.frame(
    variable = character(),
    n_loops_total = integer(),
    n_reinforcing = integer(),
    n_balancing = integer(),
    share_reinforcing = numeric(),
    share_balancing = numeric(),
    stringsAsFactors = FALSE
  )
}

cat("  Variables appearing in at least one loop:",
    nrow(variable_participation), "\n")

if (target_var %in% variable_participation$variable) {
  target_row <- variable_participation[
    variable_participation$variable == target_var,
  ]
  
  cat("  Target variable loop participation:",
      target_row$n_loops_total, "loops\n")
}
# ==========================================================
# 10. First-arrival path-based influence to readmission
# ==========================================================

cat("\nRunning first-arrival path-based qualitative influence analysis...\n")

# This section evaluates how each non-target variable may influence
# the target variable through first-arrival simple directed paths.
#
# Target variable:
#   30-Day Readmission Rate
#
# A path is classified as:
#   +  if all source-to-target paths have positive polarity
#   -  if all source-to-target paths have negative polarity
#   ±  if both positive and negative paths exist
#   0  if no directed path exists
#
# A first-arrival path terminates once the target variable is reached.
# This avoids counting additional circulation through feedback loops
# after arrival at the target.
#
# This is a path-based qualitative influence analysis. It is not an
# inverse-based Levins community-effect analysis.

path_cutoff <- if (is.null(path_cutoff_user)) {
  vcount(g) - 1L
} else {
  path_cutoff_user
}

source_vars <- setdiff(vars, target_var)

cat("  Target variable:", target_var, "\n")
cat("  Path cutoff:", path_cutoff, "links\n")
cat("  Number of source variables:", length(source_vars), "\n")


# ----------------------------------------------------------
# Helper function: calculate the sign of one directed path
# ----------------------------------------------------------

path_sign_from_ids <- function(g, vertex_ids) {
  vertex_ids <- as.integer(vertex_ids)
  
  if (length(vertex_ids) < 2) {
    return(NA_integer_)
  }
  
  from_ids <- vertex_ids[-length(vertex_ids)]
  to_ids <- vertex_ids[-1]
  
  edge_ids <- mapply(
    function(a, b) igraph::get_edge_ids(g, c(a, b), directed = TRUE),
    from_ids,
    to_ids
  )
  
  if (any(edge_ids == 0)) {
    stop("A path contains a vertex pair that is not an edge.")
  }
  
  as.integer(prod(E(g)$sign[edge_ids]))
}


# ----------------------------------------------------------
# Helper function: convert path signs into a qualitative label
# ----------------------------------------------------------

influence_symbol <- function(n_pos, n_neg) {
  if (n_pos > 0 && n_neg == 0) return("+")
  if (n_pos == 0 && n_neg > 0) return("-")
  if (n_pos > 0 && n_neg > 0) return("±")
  "0"
}


# ----------------------------------------------------------
# Helper function: enumerate first-arrival simple paths
# ----------------------------------------------------------

first_arrival_simple_paths <- function(g, source, target, cutoff) {
  if (source == target) {
    return(list())
  }
  
  igraph::all_simple_paths(
    graph = g,
    from = source,
    to = target,
    mode = "out",
    cutoff = cutoff
  )
}


# ----------------------------------------------------------
# Evaluate path-based influence for each source variable
# ----------------------------------------------------------

effects_list <- vector("list", length(source_vars))
paths_to_target_list <- list()

path_counter <- 0L

for (i in seq_along(source_vars)) {
  src <- source_vars[i]
  
  cat("  Processing source variable", i, "of", length(source_vars), "\n")
  
  paths <- first_arrival_simple_paths(
    g = g,
    source = src,
    target = target_var,
    cutoff = path_cutoff
  )
  
  if (length(paths) == 0) {
    effects_list[[i]] <- data.frame(
      source = src,
      target = target_var,
      path_based_qualitative_influence = "0",
      n_paths_total = 0L,
      n_positive_paths = 0L,
      n_negative_paths = 0L,
      shortest_positive_path = NA_integer_,
      shortest_negative_path = NA_integer_,
      shortest_any_path = NA_integer_,
      longest_path = NA_integer_,
      stringsAsFactors = FALSE
    )
    
    next
  }
  
  path_signs <- vapply(
    paths,
    function(p) path_sign_from_ids(g, as.integer(p)),
    integer(1)
  )
  
  path_lengths <- vapply(
    paths,
    function(p) length(as.integer(p)) - 1L,
    integer(1)
  )
  
  n_pos <- sum(path_signs == 1L)
  n_neg <- sum(path_signs == -1L)
  
  shortest_pos <- if (n_pos > 0) {
    min(path_lengths[path_signs == 1L])
  } else {
    NA_integer_
  }
  
  shortest_neg <- if (n_neg > 0) {
    min(path_lengths[path_signs == -1L])
  } else {
    NA_integer_
  }
  
  effects_list[[i]] <- data.frame(
    source = src,
    target = target_var,
    path_based_qualitative_influence = influence_symbol(n_pos, n_neg),
    n_paths_total = length(paths),
    n_positive_paths = n_pos,
    n_negative_paths = n_neg,
    shortest_positive_path = shortest_pos,
    shortest_negative_path = shortest_neg,
    shortest_any_path = min(path_lengths),
    longest_path = max(path_lengths),
    stringsAsFactors = FALSE
  )
  
  # Store individual diagnostic paths to the target variable.
  # This file is useful for checking how each qualitative influence
  # classification was obtained.
  
  for (j in seq_along(paths)) {
    path_counter <- path_counter + 1L
    
    path_names <- V(g)$name[as.integer(paths[[j]])]
    
    paths_to_target_list[[path_counter]] <- data.frame(
      source = src,
      target = target_var,
      path = paste(path_names, collapse = " -> "),
      path_length = path_lengths[j],
      path_sign = ifelse(path_signs[j] == 1L, "+", "-"),
      stringsAsFactors = FALSE
    )
  }
}


# ----------------------------------------------------------
# Convert path results into output tables
# ----------------------------------------------------------

path_effects_to_readmission <- do.call(rbind, effects_list)

paths_to_readmission <- if (length(paths_to_target_list) > 0) {
  do.call(rbind, paths_to_target_list)
} else {
  data.frame(
    source = character(),
    target = character(),
    path = character(),
    path_length = integer(),
    path_sign = character(),
    stringsAsFactors = FALSE
  )
}


# ----------------------------------------------------------
# Add direct effect and loop-participation information
# ----------------------------------------------------------

path_effects_to_readmission$direct_effect <- mapply(
  function(src, tgt) {
    row <- edges[edges$from == src & edges$to == tgt, ]
    
    if (nrow(row) == 0) {
      return("")
    }
    
    ifelse(row$sign[1] == 1L, "+", "-")
  },
  path_effects_to_readmission$source,
  path_effects_to_readmission$target
)

path_effects_to_readmission <- merge(
  path_effects_to_readmission,
  variable_participation,
  by.x = "source",
  by.y = "variable",
  all.x = TRUE
)

numeric_cols <- vapply(path_effects_to_readmission, is.numeric, logical(1))

path_effects_to_readmission[numeric_cols] <- lapply(
  path_effects_to_readmission[numeric_cols],
  function(x) {
    x[is.na(x)] <- 0
    x
  }
)


# ----------------------------------------------------------
# Sort output table for readability
# ----------------------------------------------------------

influence_order <- c("+", "-", "±", "0")

path_effects_to_readmission$influence_order <- match(
  path_effects_to_readmission$path_based_qualitative_influence,
  influence_order
)

path_effects_to_readmission <- path_effects_to_readmission[
  order(
    path_effects_to_readmission$influence_order,
    -path_effects_to_readmission$n_loops_total,
    path_effects_to_readmission$source
  ),
]

path_effects_to_readmission$influence_order <- NULL


# ----------------------------------------------------------
# Console summary
# ----------------------------------------------------------

cat("  Path-based influence analysis completed.\n")
cat("  Influences to", target_var, ":\n")
cat("    Positive:",
    sum(path_effects_to_readmission$path_based_qualitative_influence == "+"), "\n")
cat("    Negative:",
    sum(path_effects_to_readmission$path_based_qualitative_influence == "-"), "\n")
cat("    Ambiguous:",
    sum(path_effects_to_readmission$path_based_qualitative_influence == "±"), "\n")
cat("    No directed path:",
    sum(path_effects_to_readmission$path_based_qualitative_influence == "0"), "\n")
cat("  Individual diagnostic paths to target:",
    nrow(paths_to_readmission), "\n")

# ==========================================================
# 11. Structural summary
# ==========================================================

cat("\nPreparing structural summary table...\n")

# This summary file reports only the structural quantities that are
# directly relevant to the manuscript and the supplementary GitHub outputs:
#   - network size and validation checks
#   - feedback-loop counts and polarity
#   - loop-length categories
#   - path-based qualitative influences to the target variable
#
# Matrix-rank diagnostics are not reported because this script does not
# perform inverse-based Levins community-effect analysis and no diagonal
# self-effects are imposed.

count_loops <- function(length_bin = NULL, polarity = NULL) {
  x <- loop_df
  
  if (!is.null(length_bin)) {
    x <- x[x$length_bin == length_bin, ]
  }
  
  if (!is.null(polarity)) {
    x <- x[x$polarity == polarity, ]
  }
  
  nrow(x)
}

loops_including_target <- if (nrow(loop_df) > 0) {
  sum(vapply(
    strsplit(loop_df$loop, " -> ", fixed = TRUE),
    function(x) target_var %in% x,
    logical(1)
  ))
} else {
  0L
}

summary_df <- data.frame(
  item = c(
    "raw_nodes_in_vensim_sketch",
    "unique_variables_in_signed_graph",
    "signed_causal_links",
    "positive_links",
    "negative_links",
    "unknown_polarity_code_count",
    "unknown_polarity_code_values",
    "duplicate_variable_name_count",
    "duplicate_variable_names",
    "conflicting_duplicate_links",
    "self_links",
    "largest_feedback_core_size",
    "target_variable",
    "max_loop_length",
    "total_simple_feedback_loops",
    "reinforcing_loops",
    "balancing_loops",
    "loops_including_target_variable",
    "short_loops_leq_4_total",
    "short_loops_leq_4_reinforcing",
    "short_loops_leq_4_balancing",
    "medium_loops_5_to_8_total",
    "medium_loops_5_to_8_reinforcing",
    "medium_loops_5_to_8_balancing",
    "long_loops_9_to_16_total",
    "long_loops_9_to_16_reinforcing",
    "long_loops_9_to_16_balancing",
    "path_cutoff_to_target",
    "source_variables_assessed_for_target",
    "path_influences_to_target_positive",
    "path_influences_to_target_negative",
    "path_influences_to_target_ambiguous",
    "path_influences_to_target_zero",
    "individual_diagnostic_paths_to_target"
  ),
  value = c(
    nrow(nodes),
    length(vars),
    nrow(edges),
    sum(edges$sign == 1L),
    sum(edges$sign == -1L),
    length(unknown_codes),
    collapse_values(unknown_codes),
    length(duplicate_variable_names),
    collapse_values(duplicate_variable_names),
    nrow(conflicts),
    nrow(self_links),
    length(feedback_core_vars),
    target_var,
    max_loop_length,
    nrow(loop_df),
    sum(loop_df$sign == 1L),
    sum(loop_df$sign == -1L),
    loops_including_target,
    count_loops("short_leq_4"),
    count_loops("short_leq_4", "reinforcing"),
    count_loops("short_leq_4", "balancing"),
    count_loops("medium_5_to_8"),
    count_loops("medium_5_to_8", "reinforcing"),
    count_loops("medium_5_to_8", "balancing"),
    count_loops("long_9_to_16"),
    count_loops("long_9_to_16", "reinforcing"),
    count_loops("long_9_to_16", "balancing"),
    path_cutoff,
    nrow(path_effects_to_readmission),
    sum(path_effects_to_readmission$path_based_qualitative_influence == "+"),
    sum(path_effects_to_readmission$path_based_qualitative_influence == "-"),
    sum(path_effects_to_readmission$path_based_qualitative_influence == "±"),
    sum(path_effects_to_readmission$path_based_qualitative_influence == "0"),
    nrow(paths_to_readmission)
  ),
  stringsAsFactors = FALSE
)

cat("  Structural summary prepared.\n")
cat("  Total variables:", length(vars), "\n")
cat("  Signed causal links:", nrow(edges), "\n")
cat("  Total feedback loops:", nrow(loop_df), "\n")
cat("  Loops including target variable:", loops_including_target, "\n")
cat("  Source variables assessed for target:",
    nrow(path_effects_to_readmission), "\n")
# ==========================================================
# 12. Export CSV files
# ==========================================================

cat("\nExporting CSV files...\n")

# Export only the files needed to reproduce the structural analyses
# reported in the manuscript. Path-based outputs are restricted to
# influences on the target variable, not all source-target pairs.

write_output_csv(edges, "01_network_edges.csv")
write_output_csv(summary_df, "02_structural_summary.csv")
write_output_csv(loop_df, "03_loop_inventory.csv")
write_output_csv(variable_participation, "04_variable_loop_participation.csv")
write_output_csv(path_effects_to_readmission, "05_path_influence_to_readmission.csv")
write_output_csv(paths_to_readmission, "06_paths_to_readmission_diagnostic.csv")

cat("Done. CSV files saved in:", normalizePath(out_dir), "\n")

