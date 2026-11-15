import type { Metadata } from "next";
import { EmlCalculator } from "@/components/EmlCalculator";
import "@/components/ti-calculator.css";

export const metadata: Metadata = {
  applicationName: "EML and One",
  title: "EML and One",
  description: "a two-button calculator",
};

export default function Page() {
  return (
    <>
      <script
        dangerouslySetInnerHTML={{
          __html:
            'try{if(localStorage.getItem("eml-and-one-two-buttons")==="1")document.documentElement.classList.add("ti-two-buttons")}catch(e){}',
        }}
      />
      <EmlCalculator />
    </>
  );
}
