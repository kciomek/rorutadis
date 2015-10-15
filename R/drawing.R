#### DRAWING PLOTS

#' Draw marginal value functions and chart of alternative utilities
#'
#' This function draws marginal value functions and alternative utilities chart.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @param printLabels Whether print alternatives identifiers on marginal value
#' function plots and utility values on alternative utility chart or not
#' (default \code{TRUE}).
#' @param criteria Vector containing  \emph{0} for utility chart and/or indices
#' of criteria for which marginal value functions should be plotted.
#' If this parameter was \code{NULL} functions for all criteria and utility chart
#' will be plotted (default \code{NULL}).
#' @param plotsPerRow Number of plots per row (default \code{2}).
#' @param descending Mode of sorting alternatives on utility chart:
#' \itemize{
#' \item \code{NULL} - unsorted, preserved \code{problem$perf} order,
#' \item \code{TRUE} - sorted descending by value of utility,
#' \item \code{FALSE} - sorted ascending by value of utility.
#' }
#' 
#' @return Plot.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('c', 'g'), c(3, 3))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' drawUtilityPlots(problem, representativeFunction)
#' @import ggplot2
#' @import gridExtra
#' @export
drawUtilityPlots <- function(problem, solution, printLabels = TRUE,
                             criteria = NULL, plotsPerRow = 2,
                             descending = NULL) {
  .Deprecated("plotVF or plotComprehensiveValue")
  
  if (is.null(criteria)) {
    criteria <- c(seq_len(ncol(problem$perf)), 0)
  }
  
  graphs <- list()
  
  for (j in criteria) {
    if (j == 0) {
      graphs[[length(graphs) + 1]] <- plotComprehensiveValue(solution)
    } else {
      graphs[[length(graphs) + 1]] <- plotVF(solution, j)
    }
  }
  
  nCol <- max(floor(sqrt(length(graphs))), plotsPerRow)
  
  grid.arrange(do.call(arrangeGrob, c(graphs, list(ncol = nCol))))
}

# todo: documentation of plotVF
#' @export
plotVF <- function(solution, criterion, yAxis = "max", showAlternatives = FALSE, title = TRUE) {
  stopifnot(yAxis %in% c("adjusted", "max", "unit"))
  
  df <- as.data.frame(solution$vf[[criterion]])
  
  p <- ggplot(df, aes(x, y)) + 
    geom_point(size = 4) +
    xlab("performance") +
    ylab("value") +
    theme_bw(base_size = 20)
  
  if (!solution$generalVF[criterion]) {
    p <- p + geom_line(data = df, aes(x, y))
  }
  
  if (yAxis == "unit") {
    p <- p + ylim(0, 1)
  } else if (yAxis == "max") {
    p <- p + ylim(0, max(sapply(solution$vf, function(w) { max(w[, 2]) })))
  }
  
  if (is.logical(title)) {
    if (title) {
      p <- p + ggtitle(paste("Value function of criterion", criterion))
    }
  } else {
    p <- p + ggtitle(title)
  }
  
  if (showAlternatives) {
    # todo
    warning ("showAlternatives is not supported yet")
  }
  
  return (p)
}

# todo: documentation of plotComprehensiveValue
#' @export
plotComprehensiveValue <- function(solution, order = "alternatives", showThresholds = FALSE, title = FALSE) {
  stopifnot(order %in% c("alternatives", "asc", "desc"))
  
  if (order %in% c("asc", "desc")) {
    stop ("selected order is not supported yet")
  }
  
  nrAlternatives <- nrow(solution$alternativeValues)
  alternativeNames <- names(solution$alternativeValues)
  
  if (is.null(alternativeNames)) {
    alternativeNames <- paste("a", seq_len(nrAlternatives), sep="")
  }
  
  df <- data.frame(alternative = alternativeNames,
                   value = sapply(seq_len(nrAlternatives), function(w) { sum(solution$alternativeValues[w, ]) } ),
                   class = paste("C", solution$assignments, sep=""))
  
  p <- ggplot(data = df, aes(x = alternative, y = value, fill = class)) +
    geom_bar(stat = "identity") +
    xlab("alternative") +
    ylab("comprehensive value") +
    theme_bw(base_size = 20) +
    expand_limits(y = 1.00) +
    theme(axis.text.x = element_text(angle = 45, hjust = 1))
  
  if (is.logical(title)) {
    if (title) {
      p <- p + ggtitle("Comprehensive value of alternatives")
    }
  } else {
    p <- p + ggtitle(title)
  }
  
  if (showThresholds) {
    p <- p + geom_hline(yintercept=solution$thresholds, linetype="dashed")
  }
  
  return (p)
}
