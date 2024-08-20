from vllm import LLM
import transformers
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
import vllm

def _unique_sorted(texts, scores):
    texts_ = []
    scores_ = []
    for t, s in sorted(zip(texts, scores), key=lambda x: -x[1]):
        if t not in texts_:
            texts_.append(t)
            scores_.append(s)
    return texts_, scores_


def generate_vllm(theorem_name,path,stack,references, model, tokenizer, temperatures, num_samples, stop, max_tokens):
    texts, scores = [], []
    prompt = _make_prompt(theorem_name,path,stack,references)
    for temperature in temperatures:
        params = vllm.SamplingParams(
            n=num_samples,
            repetition_penalty=1,
            temperature=temperature,  
            use_beam_search=temperature==0.0,
            stop=stop,
            stop_token_ids=[tokenizer.eos_token_id] + tokenizer.additional_special_tokens_ids,
            max_tokens=max_tokens,
            skip_special_tokens=True,
            logprobs=0   
        )
        outputs = model.generate([prompt], params, use_tqdm=False)

        if len(outputs) == 0:
            return [], []
        for output in outputs[0].outputs:
            text = output.text.replace(tokenizer.eos_token, '') 
            score = output.cumulative_logprob
            texts.append(text)
            scores.append(score)

    texts, scores = _unique_sorted(texts, scores)
    return texts, scores

def _make_prompt(theorem,path,stack,references):
    currentState = "[" + ", ".join(" ".join(inner_list) for inner_list in stack) + "]"

    ref = "wph wps wch wth wta wcel cA cB cfv cX cF cc0 wet wze co wbr cC cN wsi c1 wrh cr wmu wla wka vx vy vz wn wi ax-mp ax-1 cc wb wa df-an wo df-or wif w3o w3a df-3an a1i wnan df-nan wxo wal cv wceq syl cR cG cK cS cvv cP adantr cW cD cV cM cY wss wral cU cT c2 cmul cle c0 cI caddc vk cH cn clt cJ wrex ex cZ cz syl3anc cmin adantl wne cE cn0 vn eqeltrd cQ c.le"

    instruction = "Based on the Metamath reference lemma [Reference] and the current proof state [Current State] provided below, please suggest the next possible proof step for theorem [Theorem]."
    input = " [Reference]" + ref + " [Current State]" + currentState
    # input = "[Theorem]" + theorem + " [Reference]" + ref + " [Current State]" + currentState
                
    prompt = instruction + input
    return prompt


def llm_init(model_path):
    llm = LLM(
        model=model_path,
        tensor_parallel_size=1,
        trust_remote_code=True,
        gpu_memory_utilization=0.4,
        dtype='float16'
    )
    tokenizer = transformers.AutoTokenizer.from_pretrained(model_path)
    tokenizer.pad_token = tokenizer.eos_token

    return llm,tokenizer