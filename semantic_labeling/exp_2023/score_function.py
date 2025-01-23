def calculate_score(predicted_semantics, gold_semantics):
    """
    Calculate the score based on Mean Reciprocal Rank (MRR), Precision, and Recall.
    
    :param predicted_semantics: List of tuples representing predicted semantic models.
    :param gold_semantics: List of tuples representing gold standard semantic models.
    :return: Dictionary containing MRR, Precision, and Recall.
    """
    def mean_reciprocal_rank(predicted, gold):
        """Calculate Mean Reciprocal Rank."""
        ranks = []
        for item in gold:
            if item in predicted:
                rank = predicted.index(item) + 1
                ranks.append(1 / rank)
        return sum(ranks) / len(gold) if ranks else 0

    def precision_recall(predicted, gold):
        """Calculate Precision and Recall."""
        predicted_set = set(predicted)
        gold_set = set(gold)
        
        true_positives = predicted_set.intersection(gold_set)
        precision = len(true_positives) / len(predicted_set) if predicted_set else 0
        recall = len(true_positives) / len(gold_set) if gold_set else 0
        
        return precision, recall

    mrr = mean_reciprocal_rank(predicted_semantics, gold_semantics)
    precision, recall = precision_recall(predicted_semantics, gold_semantics)
    
    return {
        "MRR": mrr,
        "Precision": precision,
        "Recall": recall
    }