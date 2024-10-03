from transformers import AutoTokenizer, AutoModelForSequenceClassification

class LLMModel:
    def __init__(self, model, tokenizer):
        self.tokenizer = tokenizer
        self.model = model

    def get_semantics(self, prompt):
        """Send the prompt to the LLM and get the semantic labels."""
        inputs = self.tokenizer(prompt, return_tensors="pt")
        print(inputs['input_ids'].shape)
        response = self.model(**inputs, max_new_tokens=100)
        response = self.tokenizer.decode(response.cup()[0], skip_special_tokens=True)
        return response